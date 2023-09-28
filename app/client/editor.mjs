// import * as autocomplete from "@codemirror/autocomplete"
import {EditorView, basicSetup } from "codemirror"
import { keymap } from "@codemirror/view"
import { EditorState } from "@codemirror/state"

// Custom extensions
import { markField, sentenceHover } from "./cm-extensions"

// FileManager
import { fileManager, filePanelExt } from "./fileManager.ts"

// Squirrel worker
import { SquirrelWorker } from "./squirrel-worker.ts"

// Load language syntax
import { Squirrel } from "./lang-squirrel/src/index.ts"

let worker = new 
  SquirrelWorker(fileManager,new URL('./client.bc.js', window.location));

// Bind worker and fileManager
fileManager.bindWorker(worker);

// Keybinding extension
function squirrelKeymap(view) {
  return keymap.of([{
    key: "Ctrl-Enter",
    any(view,e) { 
      // Exec/Undo to cursor 
      if (e.key == "Enter" && e.ctrlKey) {
        return worker.execToCursor(view)
      }
      // Move focus up
      if (e.key == "ArrowUp" && e.ctrlKey && e.shiftKey) {
        worker.focusRelativeN(-1)
        return true
      }
      // Move focus down
      if (e.key == "ArrowDown" && e.ctrlKey && e.shiftKey) {
        worker.focusRelativeN(1)
        return true
      }
      // Undo one sentence
      if (e.key == "ArrowUp" && e.ctrlKey) {
        worker.undo(1)
        return true
      }
      // Exec next sentence
      if (e.key == "ArrowDown" && e.ctrlKey) {
        return worker.execNextSentence(view)
      }
      return false 
    }
  }])
}

// Extension for updates 
let updateListenerExtension = EditorView.updateListener.of((update) => {
  if (update.docChanged) {
    //Boolean for system file
    fileManager.dirty = true; 
    //call updateCursor when the document has changed
    return worker.updateCursor(update)
  }
});

// Extension for filtering changes
let readOnlyTransactionFilter = EditorState.transactionFilter.of((tr) => {
  return worker.filterTransaction(tr)
});

// Create CodeMirror6 View ↓

let myview = new EditorView({
  doc:"include Basic.\n"
+"system null.type T.\n"
+"op yo : T -> T = fun(x : T) => x.\n"
+"lemma foo : empty <> empty.\n"
+"Proof.\n"
+" congruence.\n"
+" admit.\n"
+"Qed."
  ,
  extensions: [
    updateListenerExtension,
    readOnlyTransactionFilter,
    worker.simpleLezerLinter(),
    squirrelKeymap(),
    sentenceHover,
    basicSetup,
    markField,
    filePanelExt(),
    Squirrel()
  ],
  parent: input
})

//Buttons

// bind buttons to worker functions
var buttonToCursor = document.getElementById('to-cursor');
buttonToCursor.onclick = function() { 
  return worker.execToCursor(myview);
}

var buttonReset = document.getElementById('reset');
buttonReset.onclick = function() { 
  worker.reset(myview);
  return false; 
}

var buttonInfo = document.getElementById('info');
buttonInfo.onclick = function() { 
  worker.info();
  return false; 
}

var buttonUp = document.getElementById('up');
buttonUp.onclick = function() { 
  worker.undo(1)
  return false; 
}

var buttonDown = document.getElementById('down');
buttonDown.onclick = function() { 
  return worker.execNextSentence(myview);
}

var buttonFile = document.getElementById('file');
buttonFile.onclick = function() { 
  return worker.openFilePanel(myview);
}

input.onclick = (event) => {
  worker.updatePointer({x:event.x, y:event.y})
};

var runInput = document.getElementById('runinput');
runInput.addEventListener("keypress", function(event) {
  // If the user presses the "Enter" key on the keyboard
  if (event.key === "Enter") {
    return worker.run(runInput.value.toString())
  }
});

function panelClickHandler(evt) {

  var target = evt.target;

  if(target.classList.contains('caption') &&

    target.parentNode.classList.contains('flex-panel')) {

    var panel = target.parentNode;

    if(panel.classList.contains('collapsed')) {

      panel.classList.remove('collapsed');

    } else {

      var panels_cpt = document.getElementsByClassName('flex-panel').length;
      var collapsed_panels_cpt = document.getElementsByClassName('collapsed').length;

      if(collapsed_panels_cpt + 1 >= panels_cpt) // at least one panel opened
        return;

      panel.classList.add('collapsed');
    }
  }
}

var flex_container = document.getElementsByClassName('flex-container')[0];
flex_container.addEventListener('click', evt => { panelClickHandler(evt); });

worker.launch()
