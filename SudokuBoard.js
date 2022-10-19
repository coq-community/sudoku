/* This program is free software; you can redistribute it and/or      */
/* modify it under the terms of the GNU Lesser General Public License */
/* as published by the Free Software Foundation; either version 2.1   */
/* of the License, or (at your option) any later version.             */
/*                                                                    */
/* This program is distributed in the hope that it will be useful,    */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of     */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      */
/* GNU General Public License for more details.                       */
/*                                                                    */
/* You should have received a copy of the GNU Lesser General Public   */
/* License along with this program; if not, write to the Free         */
/* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA */
/* 02110-1301 USA                                                     */

'use strict';

var player = 1;
var lineColor = "#000";

var canvas = document.getElementById('sudokuBoard');
var context = canvas.getContext('2d');
var canvasSize = 300;
var sectionSize = canvasSize / 9;
canvas.width = canvasSize + canvasSize / 5;
canvas.height = canvasSize + canvasSize / 5;
var maxlinewidth = 4;
context.translate(maxlinewidth, maxlinewidth);
var message = document.getElementById('messageBoard');

function getInitialBoard(b, s) {
  for (var x = 0; x < 9; x++) {
    b.push([]);
    for (var y = 0; y < 9; y++) {
      b[x].push(Number.parseInt(s.charAt(x + 9 * y)));
    }
  }
  return;
}

var emptyText = ""
var noText = "No solution           "
var oneText = "Exactly one solution  "
var twoText = "Two solutions at least"
var init0 = '000000000000000000000000000000000000000000000000000000000000000000000000000000000';
var initS = '008160900004050200970008045005000006890000037100000400360500084002070500007049300';
var board = [];
var board1 = [];
var board2 = [];
var fontS = "12px sans-serif";
var fontL = "20px sans-serif";

function addPlayingPiece(mouse) {
  var xCoordinate;
  var yCoordinate;

  for (var x = 0; x < 9; x++) {
    for (var y = 0; y < 9; y++) {
      xCoordinate = x * sectionSize;
      yCoordinate = y * sectionSize;

      if (
        mouse.x >= xCoordinate && mouse.x <= xCoordinate + sectionSize &&
        mouse.y >= yCoordinate && mouse.y <= yCoordinate + sectionSize
      ) {
        messageBoard.innerText = emptyText;
        clearPlayingArea(xCoordinate, yCoordinate);
        board[x][y] = (board[x][y] + 1) % 10;
        board1[x][y] = 0;
        board2[x][y] = 0;
        drawNumber(board[x][y], 0, 0,
          xCoordinate, yCoordinate);
      }
    }
  }

}

function clearPlayingArea(xCoordinate, yCoordinate) {
  context.fillStyle = "#fff";
  context.fillRect(
    xCoordinate + maxlinewidth / 2,
    yCoordinate + maxlinewidth / 2,
    sectionSize - maxlinewidth,
    sectionSize - maxlinewidth
  );
}

function drawNumber(v1, v2, v3, xCoordinate, yCoordinate) {
  context.fillStyle = "#000";
  context.textAlign = 'center';
  context.textBaseline = 'middle';
  context.font = fontL;
  if (v1 != 0) {
    context.fillText(v1, xCoordinate + sectionSize / 2,
      yCoordinate + sectionSize / 2);
  } else {
    context.fillStyle = 'steelblue';
    if (v2 != 0) {
      if ((v3 == 0) || (v2 == v3)) {
        context.fillText(v2, xCoordinate + sectionSize / 2,
          yCoordinate + sectionSize / 2);
      } else {
        context.font = fontS;
        context.fillText(v2, xCoordinate + (sectionSize) / 4,
          yCoordinate + (sectionSize) / 4);
        context.fillText(v3, xCoordinate + (3 * sectionSize) / 4,
          yCoordinate + (3 * sectionSize) / 4);
      }
    }
  }
}

function drawNumbers() {
  for (var x = 0; x < 9; x++) {
    for (var y = 0; y < 9; y++) {
      drawNumber(board[x][y], board1[x][y], board2[x][y],
        x * sectionSize, y * sectionSize);
    }
  }
}

function drawLines(lineWidth, strokeStyle, b) {
  var lineStart = 0;
  var lineLength = canvasSize;
  context.lineCap = "round";
  context.lineWidth = lineWidth;
  context.strokeStyle = strokeStyle;
  context.beginPath();

  /*
   * Horizontal lines
   */
  for (var y = 0; y <= 9; y++) {
    if (b || (y % 3 == 0)) {
      context.moveTo(lineStart,
        y * sectionSize);
      context.lineTo(lineLength,
        y * sectionSize);
    }
  }

  /*
   * Vertical lines
   */
  for (var x = 0; x <= 9; x++) {
    if (b || (x % 3 == 0)) {
      context.moveTo(x * sectionSize,
        lineStart);
      context.lineTo(x * sectionSize,
        lineLength);
    }
  }

  context.stroke();
}

function resetBoard(s) {
  board = [];
  board1 = [];
  board2 = [];
  getInitialBoard(board, s);
  getInitialBoard(board1, init0);
  getInitialBoard(board2, init0);
  refreshBoard()
}

function refreshBoard() {
  if (typeof messageBoard != 'undefined') {
    messageBoard.innerText = emptyText
  }
  context.fillStyle = "#fff";
  context.fillRect(0, 0, canvasSize, canvasSize);
  drawLines(maxlinewidth / 2, lineColor, true);
  drawLines(maxlinewidth, lineColor, false);
  drawNumbers()
}

function getStringBoard() {
  var res = ''
  for (var y = 0; y < 9; y++) {
    for (var x = 0; x < 9; x++) {
      res += board[x][y]
    }
  }
  return res;
}

function solveBoard() {
  var res = solve(getStringBoard());
  board1 = [];
  board2 = [];
  getInitialBoard(board1, init0);
  getInitialBoard(board2, init0);
  if (res.charAt(0) == 'O') {
    res = res.substring(1, 82);
    board1 = [];
    getInitialBoard(board1, res);
    refreshBoard()
    messageBoard.innerText = oneText
  } else if (res.charAt(0) == 'N') {
    refreshBoard();
    messageBoard.innerText = noText
  } else if (res.charAt(0) == 'M') {
    board1 = [];
    board2 = [];
    var res1 = res.substring(1, 82);
    var res2 = res.substring(83, 164);
    getInitialBoard(board1, res1);
    getInitialBoard(board2, res2);
    refreshBoard();
    messageBoard.innerText = twoText
  }
}

var _ = resetBoard(initS, initS);

function getCanvasMousePosition(event) {
  var rect = canvas.getBoundingClientRect();

  return {
    x: event.clientX - rect.left,
    y: event.clientY - rect.top
  }
}
canvas.addEventListener('mouseup', function(event) {
  if (player === 1) {
    player = 2;
  } else {
    player = 1;
  }

  var canvasMousePosition = getCanvasMousePosition(event);
  addPlayingPiece(canvasMousePosition);
  drawLines(maxlinewidth / 2, lineColor, true);
  drawLines(maxlinewidth, lineColor, false);
});
