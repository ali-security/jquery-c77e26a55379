/*global Promise: false */
/*jshint node: true, es3: false, onevar: false, maxlen: 250, unused: true, undef: true */
/*
 * seal-browser-runner.js
 *
 * Headless QUnit runner for the jQuery test suite.
 *
 * Drives a system Chrome/Chromium through puppeteer-core, loads test/index.html
 * from a local HTTP server and forwards QUnit's own logging callbacks
 * (moduleStart / testDone / log / done) out of the page through
 * page.exposeFunction, so the report below is genuine QUnit reporting rather
 * than a scrape of the DOM.
 *
 * Usage:
 *   node test/seal-browser-runner.js [url]
 *
 * Environment:
 *   SEAL_TEST_URL       page to load (default http://127.0.0.1:8000/test/index.html?dev)
 *   SEAL_CHROME         browser executable (default /usr/bin/chromium)
 *   SEAL_TEST_TIMEOUT   overall run budget in ms (default 1800000)
 *   SEAL_QUNIT_TIMEOUT  per-test QUnit timeout in ms (default 60000, 0 disables)
 *   SEAL_VERBOSE        when "1", print one line per test instead of failures only
 *   SEAL_STALL_LIMIT    warn after this many ms without a QUnit event (default 120000)
 *   SEAL_SKIP_TESTS     "module: test name" entries, "|"- or newline-separated,
 *                       never registered with QUnit (environment-dependent tests)
 *
 * Exit status: 0 when every test passed, 1 when any test failed or the run
 * did not reach QUnit.done.
 */
"use strict";

var puppeteer = require( "puppeteer-core" );

var pageUrl = process.argv[ 2 ] || process.env.SEAL_TEST_URL ||
		"http://127.0.0.1:8000/test/index.html?dev",
	executablePath = process.env.SEAL_CHROME || "/usr/bin/chromium",
	runTimeout = parseInt( process.env.SEAL_TEST_TIMEOUT || "1800000", 10 ),
	qunitTimeout = parseInt( process.env.SEAL_QUNIT_TIMEOUT || "60000", 10 ),
	verbose = process.env.SEAL_VERBOSE === "1",
	stallLimit = parseInt( process.env.SEAL_STALL_LIMIT || "120000", 10 ),

	// "module: test name" (or a bare test name) entries, one per line or
	// separated by "|", never registered with QUnit at all.
	skipList = ( process.env.SEAL_SKIP_TESTS || "" )
		.split( /[\n|]/ )
		.map( function( entry ) {
			return entry.trim();
		} )
		.filter( function( entry ) {
			return entry.length > 0;
		} );

// Collected state, filled in from the page callbacks.
var currentModule = "(no module)",
	moduleStats = {},
	moduleOrder = [],
	failures = [],
	pendingAssertions = [],
	testCount = 0,
	assertionsPassed = 0,
	assertionsFailed = 0,
	finalSummary = null,
	pageErrors = [],
	currentTest = "(none)",
	skipped = [],
	lastEventAt = Date.now();

function out( line ) {
	process.stdout.write( line + "\n" );
}

function clip( value ) {
	var text = value === undefined ? "undefined" : String( value );
	return text.length > 400 ? text.slice( 0, 400 ) + "...(clipped)" : text;
}

/*
 * Injected into every document. Grabs QUnit the moment the suite assigns it to
 * window (qunit.js ends with `window.QUnit = QUnit`) and registers the real
 * logging callbacks. Only the top frame reports; the suite creates plenty of
 * iframes that load QUnit of their own.
 */
function installReporter() {

	/*jshint browser: true */
	if ( window !== window.top ) {
		return;
	}

	var queue = [],
		QUNIT_TIMEOUT = window.__sealQunitTimeout,

		// Grabbed at document-start, while window.JSON is still native: the ajax
		// suite temporarily replaces window.JSON with a parse-only stub
		// ("jQuery.getJSON() - Using Native JSON") and ?basic nulls it outright.
		stringify = window.JSON.stringify,
		nativeJSON = window.JSON;

	function flush() {
		if ( typeof window.__sealEmit !== "function" ) {
			window.setTimeout( flush, 25 );
			return;
		}
		while ( queue.length ) {
			window.__sealEmit( stringify.call( nativeJSON, queue.shift() ) );
		}
	}

	// A reporter fault must never propagate into the suite: QUnit runs these
	// callbacks inline, so a throw here would wedge the test that triggered it.
	function emit( kind, payload ) {
		try {
			payload.kind = kind;
			queue.push( payload );
			flush();
		} catch ( e ) {}
	}

	function dump( QUnit, value ) {
		try {
			if ( QUnit.jsDump && QUnit.jsDump.parse ) {
				return QUnit.jsDump.parse( value );
			}
		} catch ( e ) {}
		try {
			return String( value );
		} catch ( e2 ) {
			return "(unstringifiable)";
		}
	}

	/*
	 * Environment-dependent tests are dropped at declaration time rather than
	 * by editing test/unit/*.js, so the suite sources stay pristine. Entries
	 * match either the bare test name or "module: test name". By the time
	 * window.QUnit is assigned, window.test / window.asyncTest already exist
	 * (qunit.js copies QUnit onto window one statement earlier), and the unit
	 * files call them at load time with config.currentModule already set.
	 */
	function installSkips( QUnit ) {
		var skips = window.__sealSkipTests || [];

		if ( !skips.length ) {
			return;
		}

		function skipped( name ) {
			var i,
				full = ( QUnit.config.currentModule || "" ) + ": " + name;
			for ( i = 0; i < skips.length; i++ ) {
				if ( skips[ i ] === name || skips[ i ] === full ) {
					return full;
				}
			}
			return null;
		}

		function wrap( host, key ) {
			var original = host[ key ];
			if ( typeof original !== "function" ) {
				return;
			}
			host[ key ] = function( name ) {
				var full = skipped( name );
				if ( full ) {
					emit( "skip", { name: full, via: key } );
					return;
				}
				return original.apply( this, arguments );
			};
		}

		wrap( window, "test" );
		wrap( window, "asyncTest" );
		wrap( QUnit, "test" );
		wrap( QUnit, "asyncTest" );
	}

	function attach( QUnit ) {
		if ( !QUnit || QUnit.__sealAttached ) {
			return;
		}
		QUnit.__sealAttached = true;

		installSkips( QUnit );

		// Deterministic ordering: never reorder previously-failing tests first.
		QUnit.config.reorder = false;

		// A hung async test would otherwise stall the whole run.
		if ( QUNIT_TIMEOUT > 0 ) {
			QUnit.config.testTimeout = QUNIT_TIMEOUT;
		}

		QUnit.moduleStart( function( data ) {
			emit( "moduleStart", { module: data.name } );
		} );

		QUnit.testStart( function( data ) {
			emit( "testStart", {
				module: data.module === undefined ? "" : String( data.module ),
				name: String( data.name )
			} );
		} );

		QUnit.log( function( data ) {
			emit( "log", {
				result: !!data.result,
				message: data.message === undefined ? "" : String( data.message ),
				actual: data.result ? "" : dump( QUnit, data.actual ),
				expected: data.result ? "" : dump( QUnit, data.expected ),
				source: data.result || !data.source ? "" : String( data.source )
			} );
		} );

		QUnit.testDone( function( data ) {
			emit( "testDone", {
				module: data.module === undefined ? "" : String( data.module ),
				name: String( data.name ),
				failed: data.failed,
				passed: data.passed,
				total: data.total,
				runtime: data.runtime
			} );
		} );

		QUnit.done( function( data ) {
			emit( "done", {
				failed: data.failed,
				passed: data.passed,
				total: data.total,
				runtime: data.runtime
			} );
		} );
	}

	if ( window.QUnit ) {
		attach( window.QUnit );
		return;
	}

	// qunit.js has not run yet: trap the assignment.
	var stored;
	Object.defineProperty( window, "QUnit", {
		configurable: true,
		get: function() {
			return stored;
		},
		set: function( value ) {
			stored = value;
			attach( value );
		}
	} );
}

function onEvent( raw ) {
	var data;
	try {
		data = JSON.parse( raw );
	} catch ( e ) {
		out( "[runner] unparsable event: " + raw );
		return;
	}

	lastEventAt = Date.now();

	if ( data.kind === "skip" ) {
		skipped.push( data.name );
		out( "SKIP    " + data.name + "  (excluded via SEAL_SKIP_TESTS)" );

	} else if ( data.kind === "testStart" ) {
		currentTest = ( data.module || currentModule ) + ": " + data.name;

	} else if ( data.kind === "moduleStart" ) {
		currentModule = data.module || "(no module)";
		if ( !moduleStats[ currentModule ] ) {
			moduleStats[ currentModule ] = { tests: 0, failedTests: 0, passed: 0, failed: 0 };
			moduleOrder.push( currentModule );
		}
		out( "" );
		out( "== module: " + currentModule );

	} else if ( data.kind === "log" ) {
		if ( data.result ) {
			assertionsPassed++;
		} else {
			assertionsFailed++;
			pendingAssertions.push( data );
		}

	} else if ( data.kind === "testDone" ) {
		var moduleName = data.module || currentModule,
			stats = moduleStats[ moduleName ];

		if ( !stats ) {
			stats = moduleStats[ moduleName ] =
				{ tests: 0, failedTests: 0, passed: 0, failed: 0 };
			moduleOrder.push( moduleName );
		}

		testCount++;
		stats.tests++;
		stats.passed += data.passed;
		stats.failed += data.failed;

		if ( data.failed > 0 ) {
			stats.failedTests++;
			failures.push( {
				module: moduleName,
				name: data.name,
				failed: data.failed,
				total: data.total,
				assertions: pendingAssertions.slice( 0 )
			} );

			out( "FAILED  " + moduleName + ": " + data.name +
				"  (" + data.failed + "/" + data.total + " assertions failed)" );
			pendingAssertions.forEach( function( assertion, index ) {
				out( "          #" + ( index + 1 ) + " " +
					( assertion.message || "(no message)" ) );
				out( "             expected: " + clip( assertion.expected ) );
				out( "             actual:   " + clip( assertion.actual ) );
				if ( assertion.source ) {
					out( "             source:   " +
						clip( assertion.source.split( "\n" )[ 0 ] ) );
				}
			} );

		} else if ( verbose ) {
			out( "ok      " + moduleName + ": " + data.name +
				"  (" + data.total + " assertions, " + data.runtime + "ms)" );

		} else if ( testCount % 100 === 0 ) {
			out( "[runner] ... " + testCount + " tests done, " +
				assertionsFailed + " failed assertions so far" );
		}

		pendingAssertions = [];

	} else if ( data.kind === "done" ) {
		finalSummary = data;
	}
}

function report() {
	out( "" );
	out( "======================= per-module summary =======================" );
	moduleOrder.forEach( function( name ) {
		var stats = moduleStats[ name ];
		out( pad( name, 26 ) + " tests: " + pad( String( stats.tests ), 5 ) +
			" failed tests: " + pad( String( stats.failedTests ), 4 ) +
			" assertions: " + pad( String( stats.passed + stats.failed ), 6 ) +
			" failed assertions: " + stats.failed );
	} );

	out( "" );
	out( "======================= failing tests ===========================" );
	if ( !failures.length ) {
		out( "(none)" );
	}
	failures.forEach( function( failure ) {
		out( failure.module + ": " + failure.name +
			"  [" + failure.failed + "/" + failure.total + "]" );
		failure.assertions.forEach( function( assertion ) {
			out( "    - " + ( assertion.message || "(no message)" ) +
				" | expected: " + clip( assertion.expected ) +
				" | actual: " + clip( assertion.actual ) );
		} );
	} );

	if ( pageErrors.length ) {
		out( "" );
		out( "======================= page errors =============================" );
		pageErrors.forEach( function( message ) {
			out( "  " + message );
		} );
	}

	out( "" );
	out( "======================= totals ==================================" );
	out( "tests run:            " + testCount );
	out( "tests skipped:        " + skipped.length +
		( skipped.length ? " (" + skipped.join( "; " ) + ")" : "" ) );
	out( "failing tests:        " + failures.length );
	if ( finalSummary ) {
		out( "QUnit.done summary:   " + finalSummary.passed + " assertions of " +
			finalSummary.total + " passed, " + finalSummary.failed + " failed" +
			" (runtime " + finalSummary.runtime + "ms)" );
	} else {
		out( "QUnit.done summary:   NOT REACHED" );
		out( "last test started:    " + currentTest );
	}
	out( "assertions (runner):  " + ( assertionsPassed + assertionsFailed ) +
		" total, " + assertionsPassed + " passed, " + assertionsFailed + " failed" );
}

function pad( text, width ) {
	var padded = text;
	while ( padded.length < width ) {
		padded += " ";
	}
	return padded;
}

function main() {
	var browser,
		page,
		settled = false,
		timer,
		stallTimer,
		stallReported = false,
		resolveDone,
		donePromise = new Promise( function( resolve ) {
			resolveDone = resolve;
		} );

	function finish( reason ) {
		if ( !settled ) {
			settled = true;
			if ( timer ) {
				clearTimeout( timer );
			}
			if ( stallTimer ) {
				clearInterval( stallTimer );
			}
			resolveDone( reason );
		}
	}

	out( "[runner] url:     " + pageUrl );
	out( "[runner] browser: " + executablePath );
	out( "[runner] budget:  " + runTimeout + "ms, per-test QUnit timeout: " +
		qunitTimeout + "ms" );

	return puppeteer.launch( {
		executablePath: executablePath,
		headless: true,
		args: [
			"--no-sandbox",
			"--disable-dev-shm-usage",
			"--disable-gpu",
			"--window-size=1280,1024",
			"--allow-running-insecure-content",
			"--disable-features=IsolateOrigins,site-per-process"
		]
	} )
		.then( function( launched ) {
			browser = launched;
			return browser.newPage();
		} )
		.then( function( created ) {
			page = created;
			page.setDefaultTimeout( runTimeout );
			return page.setViewport( { width: 1280, height: 1024 } );
		} )
		.then( function() {
			page.on( "pageerror", function( error ) {
				pageErrors.push( "pageerror: " + error.message.split( "\n" )[ 0 ] );
			} );
			page.on( "console", function( message ) {
				if ( message.type() === "error" ) {
					pageErrors.push( "console.error: " + message.text().slice( 0, 300 ) );
				}
			} );
			page.on( "requestfailed", function( request ) {
				pageErrors.push( "requestfailed: " + request.url().slice( 0, 200 ) +
					" (" + ( request.failure() ? request.failure().errorText : "?" ) + ")" );
			} );

			return page.exposeFunction( "__sealEmit", function( raw ) {
				onEvent( raw );
				if ( finalSummary ) {
					finish( "done" );
				}
			} );
		} )
		.then( function() {
			return page.evaluateOnNewDocument(
				"window.__sealQunitTimeout = " + qunitTimeout + ";" +
				"window.__sealSkipTests = " + JSON.stringify( skipList ) + ";" );
		} )
		.then( function() {
			return page.evaluateOnNewDocument( installReporter );
		} )
		.then( function() {
			timer = setTimeout( function() {
				finish( "timeout" );
			}, runTimeout );

			// Surface a wedged test instead of sitting silent until the budget expires.
			stallTimer = setInterval( function() {
				var idle = Date.now() - lastEventAt;
				if ( idle > stallLimit && !stallReported ) {
					stallReported = true;
					out( "[runner] STALLED: no QUnit event for " + idle +
						"ms while running -> " + currentTest );
				} else if ( idle <= stallLimit ) {
					stallReported = false;
				}
			}, 10000 );
			return page.goto( pageUrl, { waitUntil: "load", timeout: runTimeout } );
		} )
		.then( function() {
			out( "[runner] page loaded, waiting for QUnit.done" );
			return donePromise;
		} )
		.then( function( reason ) {
			if ( reason === "timeout" ) {
				out( "[runner] TIMED OUT after " + runTimeout + "ms" );
			}
			return browser.close().then( function() {
				return reason;
			} );
		} )
		.then( function( reason ) {
			report();
			var bad = reason === "timeout" || !finalSummary ||
				finalSummary.failed > 0 || failures.length > 0;
			out( "" );
			out( bad ? "[runner] RESULT: FAILED" : "[runner] RESULT: PASSED" );
			process.exit( bad ? 1 : 0 );
		} )
		.catch( function( error ) {
			out( "[runner] fatal: " + ( error && error.stack || error ) );
			report();
			if ( browser ) {
				browser.close();
			}
			process.exit( 2 );
		} );
}

main();
