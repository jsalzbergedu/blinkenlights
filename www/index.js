let basic_code = `
#define tt 1

int main(int argc, char **argv) {
  int x = 0;
  x = x + 1;
  while (tt) {
    x = x + 1;
    if (x > 2) {
      break;
    }
  }
}
`

require.config({ paths: { vs: './node_modules/monaco-editor/min/vs' } });

let abstractValues = {};

/**
 * Maps line numbers to lists of string by column number
 * (<LineNumber, List<Triple<Column, Word, Property>>> where LineNumber, Column are integer,
 *  Word and Property are string).
 */
abstractValues.values = {
    // 9: [[8, "dummy", "10"]]
};

/**
 * Given model and position, choose the closest abstract element and
 * return the closest abstract element of the form
 * word (line: column): abstract property
 * or return word (line: column): no property found
 * where word is the word under the cursor
 * when no property is found.
 */
abstractValues.getValue = function(model, position) {
    let defaultWord = (model.getWordAtPosition(position) || {word: " "}).word;
    // let defaultValue = `${defaultWord}: (${position.lineNumber}:${position.column}): no property found`;
    let defaultValue = [[position.column, defaultWord, "No property found"]]
    let candidates = abstractValues.values[position.lineNumber] || defaultValue;
    // sort by distance to cursor position
    candidates.sort((x, y) => Math.abs(position.column - x[0]) - Math.abs(position.column - y[0]));
    let selected = candidates[0];
    return `"${selected[1]}" (${position.lineNumber}: ${selected[0]}): ${selected[2]}`
}

function hoverHandler(model, position) {
    document.getElementById("abstractPropertyView").innerHTML = abstractValues.getValue(model, position);
}

require(['vs/editor/editor.main'], function () {
    monaco.languages.registerHoverProvider('c', {provideHover: hoverHandler}); // Use this eventually for showing the analysis!
    // I'm thinking you can have a display below that shows the analysis
    var editor = monaco.editor.create(document.getElementById('editor'), {
        value: basic_code,
        language: 'c'
    });
});

