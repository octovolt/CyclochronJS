/**
 * Cyclochron: A Circular Sequencer
 * Copyright (C) 2021 Bill Fisher
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 * 
 * TODO:
 * Enable configuration of clock messages per step.
 * Enable turning clock and start/stop off.
 * Enable hiding the lines of symmetry.
 * Enable hiding the first beat indicator.
 * Enable rotating rhythm to random index after generation.
 * Enable rotating rhythm to best guess index(es) after generation.
 * Enable variable note-on length, rather than static at 50% of step.
 * Enable per-step editing of note-on length, velocity, pitch, etc.
 * Enable the creation of multiple cycles, allowing either polyrhythms or polymeters.
 * Enable swing.
 * Enable "gravitational pull" between polyrhythms.
 * Enable the sequencing of cycles, recursively.
 */
;(function (cyclochron, undefined) {
  const SPACE_BAR_KEY_CODE = 32;
  const ARROW_LEFT_KEY_CODE = 37;
  const ARROW_UP_KEY_CODE = 38;
  const ARROW_RIGHT_KEY_CODE = 39;
  const ARROW_DOWN_KEY_CODE = 40;
  const LETTER_G_KEY_CODE = 71;
  const LETTER_I_KEY_CODE = 73;

  const MIDI_NOTE_ON = 144; // 0x90; 
  const MIDI_NOTE_OFF = 128; // 0x80;

  const MIDI_CLOCK = 248; // 0xF8;
  const MIDI_START = 250; // 0xFA;
  const MIDI_STOP = 252; // 0xFC;

  ////////////////////////// STATE OBJECT /////////////////////////

  var state = {
    pointerDown: false,
    animationFrameAvailable: true,

    firstBeatIndex: 0,
    currentBeatIndex: 0,

    beats: [],
    cachedBeats: [],
    bpm: 120,
    midiChannel: 1,
    noteNumber: 60,
    beatDurationPercentage: 0.5,
    lastCorrectionTime: null,

    midiAccess: null,
    midiPortID: null,
    midiOutput: null,
    midiClockMessagesPerStep: 6, // assumes each step is a sixteenth note

    isPlaying: false,
    beatIntervalID: null,

    rhythmGenerator: {
      maxRests: 2,
    },
    allowOffbeatSymmetry: true,
    centerX: 0,
    centerY: 0,
    
    degrees: 0, // directly from pointer events
    degreeDelta: 0, // difference between the last degrees and current degrees
    rotationDegrees: 0, // the true degrees of rotation, while rotating
    snapDegrees: 0, // degrees of rotation to snap to

    cycleElement: null,
    firstBeatIndicatorContainer: null,
    beatMarkers: [],
    beatElements: [],
  }

  /////////////////////////// CREATE DATA /////////////////////////

  function addBeats(count) {
    for (var i = 0; i < count; i++) {
      state.beats.push({ active: false });
    }
  }

  ///////////////////////// QUERY DATA ////////////////////////////

  function isBeatActive(idx) {
    return state.beats[idx]
      ? state.beats[idx].active
      : false;
  }

  function getNextBeatIndex(idx) {
    return idx === state.beats.length - 1
      ? 0
      : idx + 1;
  }

  function getPreviousBeatIndex(idx) {
    return idx === 0
      ? state.beats.length - 1
      : idx - 1;
  }

  /**
   * Beats are assumed to be sixteenth notes, realtive to a BPM based on quarter notes.
   * Thus a 16-step cycle is assumed to be one measure long.
   */
  function getBeatLength() {
    let minute = 60 * 1000;
    let quarterNoteDuration = minute / state.bpm;
    return Math.floor(quarterNoteDuration / 4);
  }

  //////////////////////// MUTATE DATA ////////////////////////////

  function clearBeats() {
    state.beats = [];
    state.cachedBeats = [];
  }

  /**
   * Update the number of beats in the cycle, but perserve any removed 
   * beats as cached beats that we can add back later.
   * 
   * It's important to remember here that the beatCount param does not
   * map directly to a zero-indexed array. It's off by one, like the
   * length of an array.
   * 
   * @param {integer} beatCount 
   * @return {boolean} Whether the beats were updated.
   */
  function updateBeatCount(beatCount) {
    if (beatCount <= 1 || beatCount > 256) { // invalid input
      return false;
    }

    let beatCountDiff = beatCount - state.beats.length;
    if (beatCountDiff === 0) {
      // no op
      return false;
    }

    if (beatCountDiff < 0) {
      // too many beats, so cache the ones we don't need so we can get them back later
      let idx = state.beats.length - (beatCountDiff * -1);
      let removedBeats = state.beats.splice(idx);
      state.cachedBeats = removedBeats.concat(state.cachedBeats);

    } else { 
      // not enough beats, so add all the cached ones we can, and then add more if we need them
      if (state.cachedBeats.length === 0) {
        addBeats(beatCountDiff);
      } else {
        let newBeatsToAdd = beatCountDiff - state.cachedBeats.length;
        let removedCachedBeats = state.cachedBeats.splice(0, Math.max(beatCountDiff, 0));
        state.beats = state.beats.concat(removedCachedBeats);
        if (newBeatsToAdd > 0) {
          addBeats(newBeatsToAdd);
        }
      }
    }

    return true;
  }

  function activateBeat(idx) {
    if (state.beats[idx]) {
      state.beats[idx].active = true;
    }
  }

  function deactivateBeat(idx) {
    if (state.beats[idx]) {
      state.beats[idx].active = false;
    }
  }

  function updateBeats(maxRests, maxRepeats) {
    // whether the line of symmetry is on the first beat or between the last beat and the first
    var isLineOfSymmetryBetweenBeats = state.allowOffbeatSymmetry ? getCoinFlip() : false;
    adjustRotationOfLinesOfSymmetry(isLineOfSymmetryBetweenBeats);
    state.beats = generateSymmetricalRhythm(
      maxRests, 
      maxRepeats, 
      state.beats.length, 
      isLineOfSymmetryBetweenBeats,
    );
  }

  function updateCenterCoordinates() {
    let cycle = document.getElementById('cycle');
    let cycleRect = cycle.getBoundingClientRect();
    state.centerX = (cycleRect.left + cycleRect.right) / 2;
    state.centerY = (cycleRect.top + cycleRect.bottom) / 2;
  }

  function saveReferencesToElements() {
    state.cycleElement = document.getElementById('cycle');
    state.firstBeatIndicatorContainer = document.getElementById('firstBeatIndicatorContainer');
    state.beatMarkers = Array.from(document.getElementsByClassName('beatMarker'));
    state.beatElements = Array.from(document.getElementsByClassName('beat'));
  }

  function updateCycleRotationStateWithPointerData(pointerX, pointerY) {
    let lastDegrees = state.degrees;
    let radians = Math.atan2(pointerY - state.centerY, pointerX - state.centerX);

    state.degrees = radians * (180 / Math.PI);
    state.degreeDelta = lastDegrees ? state.degrees - lastDegrees : 0;
    state.rotationDegrees += state.degreeDelta;

    let beatDegrees = 360 / state.beats.length;
    if (state.rotationDegrees > state.snapDegrees + (beatDegrees / 2)) {
      // cycle circle is stepping forward clockwise by a beat,
      // thus the firstBeatIndex is stepping back by a beat.
      state.firstBeatIndex = state.firstBeatIndex === 0
        ? state.beats.length - 1
        : state.firstBeatIndex - 1;
      state.snapDegrees += beatDegrees;
    } else if (state.rotationDegrees < state.snapDegrees - (beatDegrees / 2)) {
      // cycle circle is stepping back counter-clockwise by a beat,
      // thus the firstBeatIndex is stepping forward by a beat.
      state.firstBeatIndex = state.firstBeatIndex === state.beats.length - 1
        ? 0
        : state.firstBeatIndex + 1;
      state.snapDegrees -= beatDegrees;
    }
  }

  function updateCycleRotationStateWithStepDegreeDelta(stepDegreeDelta) {
    if (stepDegreeDelta > 0) {
      state.currentBeatIndex = state.currentBeatIndex === 0
        ? state.beats.length - 1
        : state.currentBeatIndex - 1;
      state.firstBeatIndex = state.firstBeatIndex === 0
        ? state.beats.length - 1
        : state.firstBeatIndex - 1;
    } else if (stepDegreeDelta < 0) {
      state.currentBeatIndex = state.currentBeatIndex === state.beats.length - 1
        ? 0
        : state.currentBeatIndex + 1;
      state.firstBeatIndex = state.firstBeatIndex === state.beats.length - 1
        ? 0
        : state.firstBeatIndex + 1;
    }
    state.rotationDegrees += stepDegreeDelta;
    state.snapDegrees += stepDegreeDelta;
  }

  function updateCycleRotationStateForFlippedCycle() {
    let currentBeatIndex = state.currentBeatIndex + state.beats.length / 2;
    if (currentBeatIndex > state.beats.length - 1) {
      currentBeatIndex -= state.beats.length;
    }
    state.currentBeatIndex = currentBeatIndex;

    state.firstBeatIndex += state.beats.length / 2;
    if (state.firstBeatIndex > state.beats.length - 1) {
      state.firstBeatIndex -= state.beats.length;
    }

    state.rotationDegrees += 180;
    if (state.rotationDegrees > 360) {
      state.rotationDegrees -= 360;
    }
    state.snapDegrees += 180;
    if (state.snapDegrees > 360) {
      state.snapDegrees -= 360;
    }
  }

  /////////////////////// DATA HELPERS /////////////////////////////

  /**
   * Generates beats designed for a symmetrical rhythm, where 
   * the number of beats is an odd number.
   * @param {integer} maxRests Max rests that may appear in a row
   * @param {integer} maxRepeats Max repeated beats that may appear after the first beat in a series
   * @param {integer} beatCount Total beats to be generated
   */
  function genRhythmForOddCount(maxRests, maxRepeats, beatCount) {
    // An add meter rhythm presents a challenge, since the two beats at the mid point will be
    // identical due to the bi-lateral symmetry. This affects whether the beats prior may be active.
    // To solve this, we build up the beats from this mid-point, iterating back to the start.
    var beats = Array(beatCount);
    var lastIndex = beatCount - 1;
    for (var idx = lastIndex; idx >= 0; idx--) {
      if (idx === lastIndex) {
        beats[idx] = { 
          active: maxRepeats === 0 
            ? false 
            : maxRests === 1
                ? true
                : getCoinFlip() 
        };
      } else if (idx === 0) {
        var numberOfBeatsToExamine = Math.ceil(maxRepeats / 2);
        var beatsToExamine = beats.slice(1, 1 + numberOfBeatsToExamine);
        if (!beatsToExamine.some(beat => !beat.active)) {
          beats[0] = { active: false };
        } else {
          numberOfBeatsToExamine = Math.ceil(maxRests / 2);
          beatsToExamine = beats.slice(1, 1 + numberOfBeatsToExamine);
          if (!beatsToExamine.some(beat => beat.active)) {
            beats[0] = { active: true };
          } else {
            beats[0] = { active: getCoinFlip() };
          }
        }
      } else {
        let previousIndex = idx + 1;
        let isAtMaxRepeats = !beats.slice(previousIndex, previousIndex + maxRepeats + 1).some(beat => !beat.active);
        let isAtMaxRests = !beats.slice(previousIndex, previousIndex + maxRests).some(beat => beat.active);
        beats[idx] = ({ active: isAtMaxRests || (getCoinFlip() && !isAtMaxRepeats)});
      }
    }
    return beats;
  }

  function getNextStep(steps, maxRepeats, maxRests, isLineOfSymmetryBetweenBeats) {
    let idx = steps.length;
    let previousIndex = idx - 1;
    let beatsToExamineForMaxRepeats = previousIndex - maxRepeats > 0
      ? steps.slice(previousIndex - maxRepeats, idx)
      : [...steps]
          .reverse()
          .concat(steps.slice(
              !isLineOfSymmetryBetweenBeats, // concat from beginning with off beat symmetry, from index 1 for on beat
              idx,
            ))
          .slice(-maxRepeats);
    let beatsToExamineForMaxRests = idx - maxRests >= 0
      ? steps.slice(idx - maxRests, idx)
      : [...steps]
          .reverse()
          .concat(steps.slice(
            !isLineOfSymmetryBetweenBeats, 
            idx,
          ))
          .slice(-maxRests);
    let isAtMaxRepeats = steps[previousIndex].active && !beatsToExamineForMaxRepeats.some(beat => !beat.active);
    let isAtMaxRests = !steps[previousIndex].active && !beatsToExamineForMaxRests.some(beat => beat.active);
    return { active: isAtMaxRests || (getCoinFlip() && !isAtMaxRepeats) };
  }

  /**
   * Generates beats designed for a symmetrical rhythm, where  the number of beats is an even number 
   * and the bi-lateral symmetry is on a beat.
   * @param {integer} maxRests Max rests that may appear in a row
   * @param {integer} maxRepeats Max repeated beats that may appear after the first beat in a series
   * @param {integer} beatCount Total beats to be generated
   */
  function genRhythmForEvenCountWithOnBeatSymmetry(maxRests, maxRepeats, beatCount) {
    // var beats = [];
    // for (var idx = 0; idx < beatCount; idx++) {
    //   let isAtMaxRests = maxRestsReached(beats, idx, maxRests - 1);
    //   let isAtMaxRepeats = maxRepeatsReached(beats, idx, maxRepeats);
    //   beats.push({ active: isAtMaxRests || (getCoinFlip() && !isAtMaxRepeats)});
    // }
    // return beats;

    var beats = [];
    for (var idx = 0; idx < beatCount; idx++) {
      if (idx === 0) {
        beats[idx] = { active: getCoinFlip() };
      } else {
        beats[idx] = getNextStep(beats, maxRepeats, maxRests);
      }
    }
    return beats;
  }

  /**
   * Generates beats designed for a symmetrical rhythm, where  the number of beats is an even number 
   * and the bi-lateral symmetry fall between the beats.
   * @param {integer} maxRests Max rests that may appear in a row
   * @param {integer} maxRepeats Max repeated beats that may appear after the first beat in a series
   * @param {integer} beatCount Total beats to be generated
   */
  function generateRhythmForEvenCountWithOffBeatSymmetry(
    maxRests, 
    maxRepeats, 
    beatCount,
  ) {
    // The challenge here is that we have doubled hits and/or rests at both the beginning and the 
    // end of the produced rhythm. In some ways this resembles the odd meter generation, except for
    // the fact that we need to thing about the doubled hits and/or rests at both ends, instead of 
    // only one end.
    var beats = Array(beatCount);
    var lastIndex = beatCount - 1;
    for (var idx = 0; idx < beatCount; idx++) {

      // first step
      if (idx === 0) {
        beats[0] = { 
          active: maxRepeats === 0 
            ? false 
            : maxRests === 1
                ? true
                : getCoinFlip() 
        };

      // last step
      } else if (idx === lastIndex) {
        let numberOfPreviousActiveSteps = 0;
        let numberOfPreviousRests = 0;
        let examinationIndex = idx - 1;
        while (examinationIndex >= 0) {
          stepToExamine = beats[examinationIndex];
          if (numberOfPreviousRests === 0 && stepToExamine.active) {
            numberOfPreviousActiveSteps++;
          } else if (numberOfPreviousActiveSteps === 0 && !stepToExamine.active) {
            numberOfPreviousRests++;
          } else {
            break;
          }
          examinationIndex--;
        }
        let totalPossibleRepeats = (numberOfPreviousActiveSteps * 2);
        let totalPossibleRests = (numberOfPreviousRests * 2) + 2;
        if (totalPossibleRepeats <= maxRepeats && totalPossibleRests <= maxRests) {
          beats[idx] = getCoinFlip();
        } else if (totalPossibleRepeats <= maxRepeats) {
          beats[idx] = { active:true }
        } else if (totalPossibleRests <= maxRests) {
          beats[idx] = { active:false }
        } else {
          alert(
            'Failed to create rhythm. Does this ever happen? \n' +
            'Total possible repeats: ' + totalPossibleRepeats + '\n' +
            'Total possible rests: ' + totalPossibleRests + '\n',
          );
        }

      // any other step
      } else {
        let previousIndex = idx - 1;
        let maxRepeatsIndex = Math.max(previousIndex - maxRepeats, 0);
        let beatsToExamineForMaxRepeats = previousIndex - maxRepeats > 0
          ? beats.slice(maxRepeatsIndex, idx)
          : beats
              .slice(maxRepeatsIndex, idx)
              .reverse()
              .concat(beats.slice(maxRepeatsIndex, idx))
              .slice(-maxRepeats);
        let maxRestsIndex = Math.max(idx - maxRests, 0);
        let beatsToExamineForMaxRests = idx - maxRests >= 0
          ? beats.slice(maxRestsIndex, idx)
          : beats
              .slice(maxRestsIndex, idx)
              .reverse()
              .concat(beats.slice(maxRestsIndex, idx))
              .slice(-maxRests);
        let isAtMaxRepeats = beats[previousIndex].active && !beatsToExamineForMaxRepeats.some(beat => !beat.active);
        let isAtMaxRests = !beats[previousIndex].active && !beatsToExamineForMaxRests.some(beat => beat.active);
        beats[idx] = { active: isAtMaxRests || (getCoinFlip() && !isAtMaxRepeats)};
      }
    }

    return beats;
  }

  function generateSymmetricalRhythm(
    maxRests, 
    maxRepeats, 
    beatCount, 
    isLineOfSymmetryBetweenBeats,
  ) {
    // even: half. odd: less than half.
    var halfBeatCount = Math.floor(beatCount / 2);

    // does the cycle have an odd number of beats
    var oddNumberOfBeats = beatCount % 2;

    var beats = [];
    if (oddNumberOfBeats) {
      beats = genRhythmForOddCount(maxRests, maxRepeats, halfBeatCount + 1);
    } else if (!isLineOfSymmetryBetweenBeats) {
      beats = genRhythmForEvenCountWithOnBeatSymmetry(maxRests, maxRepeats, halfBeatCount);
    } else {
      beats = generateRhythmForEvenCountWithOffBeatSymmetry(maxRests, maxRepeats, halfBeatCount)
    }

    // create second half of rhythm
    for (var idx = 0; idx < halfBeatCount; idx++) {
      let index = halfBeatCount + idx + oddNumberOfBeats;
      // Determine middle beat of a rhythm with an even count and on beat symmetry
      if (idx === 0 && !oddNumberOfBeats && !isLineOfSymmetryBetweenBeats) {
        var numberOfBeatsToExamine = maxRepeats === 0
          ? 1
          : Math.ceil(maxRepeats / 2);
        var beatsToExamine = beats.slice(-numberOfBeatsToExamine);
        if (!beatsToExamine.some(beat => !beat.active)) { // all examined beats are active
          beats[index] = { active: false };
        } else {
          numberOfBeatsToExamine = Math.ceil(maxRests / 2);
          beatsToExamine = beats.slice(-numberOfBeatsToExamine);
          if (!beatsToExamine.some(beat => beat.active)) { // all examined beats are rests
            beats[index] = { active: true };
          } else {
            beats[index] = { active: getCoinFlip() };
          }
        }
      } else {
        let mirrorBeatIndex = halfBeatCount - idx - isLineOfSymmetryBetweenBeats;
        beats[index] = beats[mirrorBeatIndex];
      }
    }
    return beats;
  }

  /////////////////////////// MODIFY UI ///////////////////////////

  /**
   * Remove all the elements in the provided HTMLCollection.
   * @param {HTMLCollection} collection 
   */
  function removeHTMLCollection(collection) {
    while (collection.length > 0) {
      collection[0].remove();
    }
  }

  /**
   * Add new beat elements based on an array of beats.
   * @param {Array<Beat>} beats
   * @param {HTMLElement} cycle
   */
  function addBeatElements(beats, cycle) {
    let beatElements = beats.map((_beat, idx) => {
      let beatElement = document.createElement('div');
      beatElement.setAttribute(
        'class',
        isBeatActive(idx)
          ? 'beat beatActive'
          : 'beat'
      );
      
      let rotationDegrees = (idx * (360 / state.beats.length)) + 'deg';
      beatElement.style.transform = `rotate(${rotationDegrees}) translateY(-50%)`;

      let beatMarker = document.createElement('div');
      beatMarker.setAttribute('class', 'beatMarker');
      beatElement.append(beatMarker);

      beatElement.addEventListener('click', (e) => {
        handleBeatClick(beatElement, idx);
      });

      return beatElement;
    });
    cycle.append(...beatElements);
  }

  function layoutBeats() {
    let cycle = document.getElementById('cycle');
    removeHTMLCollection(document.getElementsByClassName('beat'));
    addBeatElements(state.beats, cycle);
    saveReferencesToElements(); // must be called last
  }

  function enableOffbeatSymmetryCheckboxIfNeeded() {
    let offbeatSymmetry = document.getElementById('offbeatSymmetry');
    if (state.allowOffbeatSymmetry) {
      offbeatSymmetry.checked = true;
    } else {
      offbeatSymmetry.checked = false;
    }
    offbeatSymmetry.disabled = false;
    let label = offbeatSymmetry.previousElementSibling;
    label.removeAttribute('class');
  }

  function disableOffbeatSymmetryCheckbox() {
    let offbeatSymmetry = document.getElementById('offbeatSymmetry');
    offbeatSymmetry.checked = false;
    offbeatSymmetry.disabled = true;
    let label = offbeatSymmetry.previousElementSibling;
    label.setAttribute('class', 'disabled');
  }

  function adjustMaxRestsIfNeeded() {
    if (state.beats.length % 2 && parseInt(document.getElementById('maxRepeats').value) === 0) {
      let maxRests = document.getElementById('maxRests');
      if (parseInt(maxRests.value) === 1) {
        maxRests.value = 2;
      }
    }
  }

  function adjustMaxRepeatsIfNeeded() {
    if (state.beats.length % 2 && parseInt(document.getElementById('maxRests').value) === 1) {
      let maxRepeats = document.getElementById('maxRepeats');
      if (parseInt(maxRepeats.value) === 0) {
        maxRepeats.value = 1;
      }
    }
  }

  function rotateCycleElement(degrees) {
    state.cycleElement.style.transform = `rotate(${degrees}deg)`;
  }

  function rotateFirstBeatIndicatorContainer(degrees) {
    state.firstBeatIndicatorContainer.style.transform = `rotate(${-degrees}deg) translateY(-50%)`;
  }

  function adjustRotationOfLinesOfSymmetry(isLineOfSymmetryBetweenBeats) {
    let degrees = isLineOfSymmetryBetweenBeats
      ? -(360 / state.beats.length) / 2
      : 0;
    document.getElementById('symmetry').style.transform = `rotate(${degrees}deg)`;
    document.getElementById('crossSymmetry').style.transform = `rotate(${degrees}deg)`;
  }

  /**
   * Updates the options in the MIDI Output Port select element.
   * Worth noting that a MIDIOutputMap is a maplike object 
   * of type maplike<DOMString, MIDIOutput>.
   * See https://www.w3.org/TR/webmidi/#idl-def-MIDIOutputMap 
   * @param {MIDIOutputMap} outputs 
   */
  function updatePortSelectorOptions(outputs) {
    let portSelector = document.getElementById('midiOutputPort');
    for (child of portSelector.children) {
      child.remove();
    }
    if (outputs.size) {
      for (output of outputs.values()) {
        let option = document.createElement("option");
        let name = output.name.length < 15
          ? output.name
          : output.name.slice(0, 15) + '...';
        option.text = name;
        option.value = output.id;
        portSelector.add(option);
      }
    } else {
      let option = document.createElement("option");
      option.text = 'NONE';
      portSelector.add(option);
    }
  }

  function clearBeatMarkers() {
    for (marker of state.beatMarkers) {
      marker.classList.remove('playing');
    }
  }

  //////////////////////////// UTILS & HELPERS ////////////////////////

  function getCoinFlip() {
    return Math.random(0, 1) < 0.5;
  }

  function shouldAllowOffbeatSymmetry(beatCount, maxRests, maxRepeats) {
    if (beatCount % 2 || maxRests === 1 || maxRepeats === 0) {
      return false;
    }
    return true;
  }

  // function getRandomInt(min, max) {
  //   min = Math.ceil(min);
  //   max = Math.floor(max);
  //   return Math.floor(Math.random() * (max - min + 1)) + min;
  // }

  /////////////// MIDI SET UP AND SEQUENCER PLAYBACK ////////////////

  /**
   * Request MIDI access and set up success and failure handlers.
   * See https://www.w3.org/TR/webmidi/#requestmidiaccess
   */
  function setUpMidi() {
    navigator.requestMIDIAccess()
      .then(handleMidiSuccess, handleMidiFailure);
  }

  /**
   * Send a note-on message followed by a note-off message.
   * @param {integer} noteDuration Length of time between note-on and note-off messages. 
   */
  function sendNote(noteDuration) {
    let noteOnMessage = [
      MIDI_NOTE_ON + state.midiChannel - 1, 
      noteNumber, 
      0x7f,
    ];
    let noteOffMessage = [
      MIDI_NOTE_OFF + state.midiChannel - 1,
      noteNumber,
      0x00,
    ];
    state.midiOutput?.send(noteOnMessage);
    state.midiOutput?.send(noteOffMessage, window.performance.now() + noteDuration);   
  }

  /**
   * Note that the duration here is is the full length of the beat.
   * @param {integer} beatLength Full length of the beat in milliseconds.
   */
  function sendClock(beatLength) {
    let clockTime = Math.floor(beatLength / state.midiClockMessagesPerStep);
    let now = window.performance.now();
    for (var i = 0; i < state.midiClockMessagesPerStep; i++) {
      if (i === 0) {
        state.midiOutput?.send([MIDI_CLOCK]);
      } else {
        state.midiOutput?.send([MIDI_CLOCK], now + (clockTime * i));
      } 
    }
  }

  /**
   * Send all note and clock messages related to the beat at the given index.
   * @param {integer} idx Index of the beat. 
   * @param {integer} beatLength Full length of the beat in milliseconds. 
   * Note that this is not the same as the note-on length.
   */
  function playBeatAtIndex(idx, beatLength) {
    sendClock(beatLength);
    let prevIdx = getPreviousBeatIndex(idx);
    let prevBeatMarker = state.beatMarkers[prevIdx];
    if (!prevBeatMarker) {
      console.log('idx', idx, 'prevIdx', prevIdx);
    }
    prevBeatMarker.classList.remove('playing');
    state.beatMarkers[idx].classList.add('playing');
    state.currentBeatIndex = idx;

    if (state.beats[idx].active) {  
      let duration = beatLength / 2;
      sendNote(duration);
      state.beatElements[idx].classList.add('playing');
      window.setTimeout(() => {
        state.beatElements[idx].classList.remove('playing');
      }, duration);
    }
  }

  // function correctLoop(idx, beatLength) {
  //   let timeSinceLastCorrection = window.performance.now() - state.lastCorrectionTime;
  //   let correction = timeSinceLastCorrection % beatLength;
  //   beatLength = 
  //     correction < beatLength / 2 
  //     ? beatLength + correction 
  //     : correction;

  //   if (correction !== beatLength) {
  //     stopLoop();
  //     window.setTimeout(() => {
  //       playBeatAtIndex(idx, correction);
  //       startLoop(getNextBeatIndex(idx));
  //     }, correction);
  //   }
  // }

  function startLoop(startIdx) {
    if (state.lastCorrectionTime === null) {
      state.lastCorrectionTime = window.performance.now();
    }
    state.currentBeatIndex = startIdx;
    var beatLength = getBeatLength();
    state.beatIntervalID = window.setInterval(
      () => {
        playBeatAtIndex(state.currentBeatIndex, beatLength);
        state.currentBeatIndex = getNextBeatIndex(state.currentBeatIndex);
      },
      Math.floor(getBeatLength()),
    );
  }

  function stopLoop() {
    window.clearInterval(state.beatIntervalID);
  }

  function startSequencer() {
    if (state.isPlaying) {
      stopLoop();
    } else {
      state.isPlaying = true;
      state.midiOutput?.send([MIDI_START]);
    }
    clearBeatMarkers();
    playBeatAtIndex(state.firstBeatIndex, getBeatLength());
    startLoop(
      state.firstBeatIndex + 1 === state.beats.length
        ? 0
        : state.firstBeatIndex + 1,
    );
  }

  function stopSequencer() {
    state.isPlaying = false;
    stopLoop();
    state.midiOutput?.send([MIDI_STOP]);
  }

  /////////////////////// EVENT HANDLERS ///////////////////////////

  function setUpEventHandlers() {
    document
      .getElementById('graphicsContainer')
      .addEventListener('pointerdown', handleCyclePointerDown);
    document
      .getElementById('graphicsContainer')
      .addEventListener('pointermove', handleCyclePointerMove);
    document
      .getElementById('graphicsContainer')
      .addEventListener('pointerup', handleCyclePointerUp);
    document
      .getElementById('configurationContainer')
      .addEventListener('submit', (e) => {
        e.preventDefault();
      });
    document
      .getElementById('beats')
      .addEventListener('input', handleBeatsChange);
    document
      .getElementById('bpm')
      .addEventListener('input', handleBPMChange);
    document
      .getElementById('midiChannel')
      .addEventListener('change', handleMIDIChannelChange);
    document
      .getElementById('noteNumber')
      .addEventListener('input', handleNoteNumberChange);
    document
      .getElementById('startButton')
      .addEventListener('click', handleStartButtonClicked);
    document
      .getElementById('stopButton')
      .addEventListener('click', handleStopButtonClicked);
    document
      .getElementById('maxRests')
      .addEventListener('change', handleMaxRestsChange);
    document
      .getElementById('maxRepeats')
      .addEventListener('change', handleMaxRepeatsChange);
    document
      .getElementById('offbeatSymmetry')
      .addEventListener('click', handleOffbeatSymmetryCheckboxChange);
    document
      .getElementById('generateButton')
      .addEventListener('click', handleGenerateButtonClicked);
    document
      .getElementById('clearButton')
      .addEventListener('click', handleClearButtonClicked);
    document
      .addEventListener('keydown', handleKeyDown);
  }

  function handleBeatsChange(event) {
    if (updateBeatCount(parseInt(event.target.value))) {
      layoutBeats();
      enableOrDisableOffbeatSymmetryIfNeeded();
      adjustMaxRepeatsIfNeeded();
    }
  }

  function handleBeatClick(beatElement, idx) {
    if (isBeatActive(idx)) {
      deactivateBeat(idx);
      beatElement.setAttribute('class', 'beat');
    } else {
      activateBeat(idx);
      beatElement.setAttribute('class', 'beat beatActive');
    }
  }

  function handleMaxRestsChange(e) {
    enableOrDisableOffbeatSymmetryIfNeeded();
    adjustMaxRepeatsIfNeeded()
  }

  function handleMaxRepeatsChange(e) {
    enableOrDisableOffbeatSymmetryIfNeeded();
    adjustMaxRestsIfNeeded();
  }

  function handleOffbeatSymmetryCheckboxChange(e) {
    if (e.target.checked === true) {
      state.allowOffbeatSymmetry = true;
    } else {
      state.allowOffbeatSymmetry = false;
    }
  }

  function handleGenerateButtonClicked(e) {
    clearBeats();
    let beatCount = parseInt(document.getElementById('beats').value);
    addBeats(beatCount);
    let maxRests = parseInt(document.getElementById('maxRests').value);
    let maxRepeats = parseInt(document.getElementById('maxRepeats').value);
    updateBeats(maxRests, maxRepeats);
    layoutBeats();
  }

  function handleClearButtonClicked(e) {
    if (state.isPlaying) {
      stopSequencer();
    }
    clearBeats();
    let beatCount = parseInt(document.getElementById('beats').value);
    addBeats(beatCount);
    layoutBeats();
  }

  function enableOrDisableOffbeatSymmetryIfNeeded() {
    let beatCount = state.beats.length;
    let maxRests = parseInt(document.getElementById('maxRests').value);
    let maxRepeats = parseInt(document.getElementById('maxRepeats').value);
    if (shouldAllowOffbeatSymmetry(beatCount, maxRests, maxRepeats)) {
      state.allowOffbeatSymmetry = true;
      enableOffbeatSymmetryCheckboxIfNeeded();
    } else {
      state.allowOffbeatSymmetry = false;
      disableOffbeatSymmetryCheckbox();
    }
  }

  function handleCyclePointerDown(e) {
    var path = e.composedPath();
    if (path.includes(state.cycleElement)) {
      return;
    }
    let radians = Math.atan2(e.y - state.centerY, e.x - state.centerX);
    state.degrees = radians * (180 / Math.PI);
    state.pointerDown = true;
  }
 
  function handleCyclePointerMove(e) {
    if (state.pointerDown && state.animationFrameAvailable) {
      var path = e.composedPath();
      if (path.includes(state.cycleElement)) {
        return;
      }
      state.animationFrameAvailable = false;
      window.requestAnimationFrame((time) => {
        updateCycleRotationStateWithPointerData(e.x, e.y);
        rotateCycleElement(state.rotationDegrees);
        rotateFirstBeatIndicatorContainer(state.rotationDegrees);

        state.animationFrameAvailable = true;
      })
    }
  }

  function handleCyclePointerUp(e) {
    if (!state.pointerDown) {
      return;
    }
    state.rotationDegrees = state.snapDegrees;
    rotateCycleElement(state.snapDegrees);
    rotateFirstBeatIndicatorContainer(state.snapDegrees);
    state.pointerDown = false;
  }

  function handleBPMChange(e) {
    state.bpm = parseInt(e.target.value);
  }

  function handleMIDIChannelChange(e) {
    state.midiChannel = parseInt(e.target.value);
  }

  function handleNoteNumberChange(e) {
    state.noteNumber = parseInt(e.target.value);
  }

  function handleStartButtonClicked(e) {
    startSequencer();
  }

  function handleStopButtonClicked(e) {
    stopSequencer();
  }

  /**
   * Set up in setUpMidi().
   * @param {MIDIAccess} access 
   * @param {MIDIOptions} __options Unused.
   */
  function handleMidiSuccess(access, __options) {
    state.midiAccess = access;
    updatePortSelectorOptions(access.outputs);
    if (access.outputs.size) {
      state.midiPortID = access.outputs.values().next().value.id;
      state.midiOutput = access.outputs.get(state.midiPortID);
      state.midiOutput.open();
    }
    // Delay setting this up so the initial port opening will not fire this event.
    setTimeout(() => {
      state.midiAccess.onstatechange = handleMidiStateChange;
    }, 2000);
  }

  /**
   * Set up in setUpMidi().
   * @param {DOMException} error 
   */
  function handleMidiFailure(error) {
    alert(
      'Failed to get MIDI access.\n' +
      'Please note that Cyclochron does not use MIDI SysEx, ' +
      'which is the only portion of the Web MIDI API that has any true security concern. \n' + 
      'See https://www.w3.org/TR/webmidi/#security-and-privacy-considerations-of-midi. \n'
      (error instanceof DOMException) ? error.name + '\n' + error.message : error,
    );
  }

  /**
   * Set up in handleMidiSuccess().
   * @param {MIDIConnectionEvent} e 
   */
  function handleMidiStateChange(e) {
    // let port = e.port;
    // // Print information about the (dis)connected MIDI controller
    // alert(
    //   port.name + '\n' + 
    //   port.manufacturer + '\n' + 
    //   'MIDIPortDeviceState: ' + port.state + '\n' +
    //   'MIDIPortConnectionState: ' + port.connection
    // );
    let access = state.midiAccess;
    updatePortSelectorOptions(access);
    if (access.outputs.values().size) {
      state.midiPortID = access.outputs.values().next().value.id;
      state.midiOutput = access.outputs.get(state.midiPortID);
      state.midiOutput.open();
    }
  }

  function handleKeyDown(e) {
    var degreeDelta = 0;
    switch (e.keyCode) {
      case SPACE_BAR_KEY_CODE:
        e.preventDefault();
        if (state.isPlaying) {
          stopSequencer();
        } else {
          startSequencer();
        }
        break;
      case ARROW_DOWN_KEY_CODE:
      case ARROW_UP_KEY_CODE:
        e.preventDefault();
        if (state.beats.length % 2) {
          // flipping an odd meter rhythm does not make sense because we don't know where to put
          // the first beat.
          break;
        }
        updateCycleRotationStateForFlippedCycle();
        clearBeatMarkers();
        rotateCycleElement(state.rotationDegrees);
        rotateFirstBeatIndicatorContainer(state.rotationDegrees);
        break;
      case ARROW_RIGHT_KEY_CODE:
        e.preventDefault();
        degreeDelta = 360 / state.beats.length;
        updateCycleRotationStateWithStepDegreeDelta(degreeDelta);
        clearBeatMarkers();
        rotateCycleElement(state.rotationDegrees);
        rotateFirstBeatIndicatorContainer(state.rotationDegrees);
        break;
      case ARROW_LEFT_KEY_CODE:
        e.preventDefault();
        degreeDelta = (360 / state.beats.length) * -1;
        updateCycleRotationStateWithStepDegreeDelta(degreeDelta);
        clearBeatMarkers();
        rotateCycleElement(state.rotationDegrees);
        rotateFirstBeatIndicatorContainer(state.rotationDegrees);
        break;
      case LETTER_G_KEY_CODE:
        handleGenerateButtonClicked();
        break;
      case LETTER_I_KEY_CODE:
        state.beats = state.beats.map(beat => {
          return { active: !beat.active };
        });
        layoutBeats();
        break;
    }
  }

  /////////////////////////// INIT FUNCTION ////////////////////////////

  cyclochron.init = function () {
    // state
    addBeats(parseInt(document.getElementById('beats').value));
    updateCenterCoordinates();
    
    // presentation
    layoutBeats();

    // behavior
    setUpMidi();
    setUpEventHandlers();
  }

}( window.cyclochron = window.cyclochron || {} ));

window.cyclochron.init();
