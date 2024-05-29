import { PRINT_ALL_ERRORS } from "./config";

export class EasycryptError {
	constructor(
		public startLine: number,
		public startColumn: number,
		public endLine: number,
		public endColumn: number,
		public msg: string,
	) {}
}

class ProcessedStderr {
	constructor(
		public errors: EasycryptError[],
		public successes: string[],
	) { }
}

export function getMostRecentGoal(stdout: string): string {
	// Each output from easycrypt starts with something like [3|check]>
	const logs = stdout
		.split(/\[\d+\|[a-z]+\]>\n/)
		.map((line) => line || "");
	
	// Logs printing a goal start with either "Current goal" or "No more goals"
	// and we only care about the last one printed
	// If pragma Goals:printall. is in play, this last single entry will include all the goals in play
	return logs
		.reverse()
		.find((goalString) =>
			goalString.startsWith("Current goal") ||
			goalString.startsWith("No more goals")
		) || "";
}

// Stderr contains both errors as well as the logging of objects added to the file's context
export function processStderr(stderr: string): ProcessedStderr {
	const lines = stderr.split('\n');
	
	return new ProcessedStderr (
		getErrors(stderr),
		getSuccesses(stderr),
	);
}

//Format:
//: line 0 (1) to line 5 (9): error message
const errorLineRegexp = new RegExp(/: line (\d+) \((\d+)\) to line (\d+) \((\d+)\): (.*)/);

// Extracts specifically the easycrypt errors from the stderr log
function getErrors(stderr: string): EasycryptError[] {
	const lines = stderr
		.split('\n')
		.map((line) => line || ""); // replace any undefined with the empty string
	const errors = lines
		.map((line) => errorLineRegexp.exec(line)) // null if it doesn't match, [match, capture groups..] if it does
		.map((matchResult) =>      // package the results into EasycryptErrors
			matchResult && // null if matchResult is null
			new EasycryptError(
				parseInt(matchResult[1]), // error start line
				parseInt(matchResult[2]), // error start column
				parseInt(matchResult[3]), // error end line
				parseInt(matchResult[4]), // error end column
				matchResult[5]            // error message
			)
		)
		.filter((matchResult): matchResult is EasycryptError => matchResult !== null);
	
	// Whether or not to print all errors is configurable because
	// any after the first are not as reliable, fixing the first can change them
	if (errors.length === 0) {
		return [];
	} else if (PRINT_ALL_ERRORS) {
		return errors;
	} else {
		return [errors[0]];
	}
}

function getSuccesses(stderr: string): string[] {
	const lines = stderr.split('\n');
	return lines
		.slice(0, lines.findIndex((line) => errorLineRegexp.test(line))) // Only keep logs from before any errors
		.filter((line) => line.startsWith("added "))     // Looking for lines like "added axiom: `q_axiom'"
		.map((line) => line.slice("added ".length))      // Remove the added prefix to just get a collection of the created objects
}
