const QR_COUNT = 6;
const QR_VERSION = 2;
const QR_SIZE = 17 + QR_VERSION * 4;
const DATA_CODEWORDS = 34;
const ECC_CODEWORDS = 10;
const REMAINDER_BITS = 7;
const QUIET_ZONE = 1;

const qrImage = document.getElementById("qrImage");
const refreshHotspot = document.getElementById("refreshHotspot");
const passStage = document.getElementById("passStage");
const passBackground = document.getElementById("passBackground");
const backHotspot = document.getElementById("backHotspot");
const mobilePassHotspot = document.getElementById("mobilePassHotspot");

let currentIndex = 0;
let qrItems = [];

function makeToken(index) {
  const bytes = new Uint8Array(8);
  crypto.getRandomValues(bytes);
  const randomPart = Array.from(bytes, (value) => value.toString(16).padStart(2, "0")).join("");
  return `LIB${index + 1}-${randomPart}`.toUpperCase();
}

function getBit(value, index) {
  return ((value >>> index) & 1) !== 0;
}

function initGaloisField() {
  const exp = new Array(512).fill(0);
  const log = new Array(256).fill(0);
  let value = 1;

  for (let i = 0; i < 255; i += 1) {
    exp[i] = value;
    log[value] = i;
    value <<= 1;
    if (value & 0x100) {
      value ^= 0x11d;
    }
  }

  for (let i = 255; i < 512; i += 1) {
    exp[i] = exp[i - 255];
  }

  return { exp, log };
}

const GF = initGaloisField();

function gfMultiply(a, b) {
  if (a === 0 || b === 0) {
    return 0;
  }
  return GF.exp[GF.log[a] + GF.log[b]];
}

function makeGenerator(degree) {
  let poly = [1];
  for (let i = 0; i < degree; i += 1) {
    const next = new Array(poly.length + 1).fill(0);
    for (let j = 0; j < poly.length; j += 1) {
      next[j] ^= gfMultiply(poly[j], GF.exp[i]);
      next[j + 1] ^= poly[j];
    }
    poly = next;
  }
  return poly;
}

function makeErrorCorrection(data) {
  const generator = makeGenerator(ECC_CODEWORDS);
  const result = new Array(ECC_CODEWORDS).fill(0);

  data.forEach((codeword) => {
    const factor = codeword ^ result.shift();
    result.push(0);
    for (let i = 0; i < ECC_CODEWORDS; i += 1) {
      result[i] ^= gfMultiply(generator[i], factor);
    }
  });

  return result;
}

function appendBits(bits, value, length) {
  for (let i = length - 1; i >= 0; i -= 1) {
    bits.push((value >>> i) & 1);
  }
}

function encodeDataCodewords(text) {
  const encoder = new TextEncoder();
  const bytes = Array.from(encoder.encode(text));
  const bits = [];

  appendBits(bits, 0b0100, 4);
  appendBits(bits, bytes.length, 8);
  bytes.forEach((byte) => appendBits(bits, byte, 8));
  appendBits(bits, 0, Math.min(4, DATA_CODEWORDS * 8 - bits.length));

  while (bits.length % 8 !== 0) {
    bits.push(0);
  }

  const codewords = [];
  for (let i = 0; i < bits.length; i += 8) {
    let codeword = 0;
    for (let j = 0; j < 8; j += 1) {
      codeword = (codeword << 1) | bits[i + j];
    }
    codewords.push(codeword);
  }

  for (let pad = 0xec; codewords.length < DATA_CODEWORDS; pad = pad === 0xec ? 0x11 : 0xec) {
    codewords.push(pad);
  }

  return codewords;
}

function makeMatrix() {
  return Array.from({ length: QR_SIZE }, () =>
    Array.from({ length: QR_SIZE }, () => ({ value: false, reserved: false })),
  );
}

function setModule(matrix, x, y, value, reserved = true) {
  if (x < 0 || y < 0 || x >= QR_SIZE || y >= QR_SIZE) {
    return;
  }
  matrix[y][x] = { value, reserved };
}

function drawFinder(matrix, startX, startY) {
  for (let y = -1; y <= 7; y += 1) {
    for (let x = -1; x <= 7; x += 1) {
      const xx = startX + x;
      const yy = startY + y;
      const edge = x === 0 || x === 6 || y === 0 || y === 6;
      const center = x >= 2 && x <= 4 && y >= 2 && y <= 4;
      setModule(matrix, xx, yy, edge || center, true);
    }
  }
}

function drawAlignment(matrix, centerX, centerY) {
  for (let y = -2; y <= 2; y += 1) {
    for (let x = -2; x <= 2; x += 1) {
      const edge = Math.abs(x) === 2 || Math.abs(y) === 2;
      const center = x === 0 && y === 0;
      setModule(matrix, centerX + x, centerY + y, edge || center, true);
    }
  }
}

function drawFunctionPatterns(matrix) {
  drawFinder(matrix, 0, 0);
  drawFinder(matrix, QR_SIZE - 7, 0);
  drawFinder(matrix, 0, QR_SIZE - 7);
  drawAlignment(matrix, 18, 18);

  for (let i = 8; i < QR_SIZE - 8; i += 1) {
    const value = i % 2 === 0;
    setModule(matrix, i, 6, value, true);
    setModule(matrix, 6, i, value, true);
  }

  setModule(matrix, 8, QR_SIZE - 8, true, true);

  for (let i = 0; i < 9; i += 1) {
    if (i !== 6) {
      setModule(matrix, 8, i, false, true);
      setModule(matrix, i, 8, false, true);
    }
  }

  for (let i = QR_SIZE - 8; i < QR_SIZE; i += 1) {
    setModule(matrix, 8, i, false, true);
    setModule(matrix, i, 8, false, true);
  }
}

function shouldMask(x, y) {
  return (x + y) % 2 === 0;
}

function drawData(matrix, codewords) {
  const bits = [];
  codewords.forEach((codeword) => appendBits(bits, codeword, 8));
  appendBits(bits, 0, REMAINDER_BITS);

  let bitIndex = 0;
  let upward = true;

  for (let right = QR_SIZE - 1; right >= 1; right -= 2) {
    if (right === 6) {
      right -= 1;
    }

    for (let vertical = 0; vertical < QR_SIZE; vertical += 1) {
      const y = upward ? QR_SIZE - 1 - vertical : vertical;

      for (let offset = 0; offset < 2; offset += 1) {
        const x = right - offset;
        if (!matrix[y][x].reserved) {
          const bit = bitIndex < bits.length ? bits[bitIndex] === 1 : false;
          matrix[y][x] = { value: bit !== shouldMask(x, y), reserved: false };
          bitIndex += 1;
        }
      }
    }

    upward = !upward;
  }
}

function drawFormatBits(matrix) {
  const format = 0b111011111000100;

  for (let i = 0; i <= 5; i += 1) {
    setModule(matrix, 8, i, getBit(format, i), true);
  }
  setModule(matrix, 8, 7, getBit(format, 6), true);
  setModule(matrix, 8, 8, getBit(format, 7), true);
  setModule(matrix, 7, 8, getBit(format, 8), true);
  for (let i = 9; i < 15; i += 1) {
    setModule(matrix, 14 - i, 8, getBit(format, i), true);
  }

  for (let i = 0; i < 8; i += 1) {
    setModule(matrix, QR_SIZE - 1 - i, 8, getBit(format, i), true);
  }
  for (let i = 8; i < 15; i += 1) {
    setModule(matrix, 8, QR_SIZE - 15 + i, getBit(format, i), true);
  }
  setModule(matrix, 8, QR_SIZE - 8, true, true);
}

function createQrMatrix(token) {
  const matrix = makeMatrix();
  const data = encodeDataCodewords(token);
  const ecc = makeErrorCorrection(data);

  drawFunctionPatterns(matrix);
  drawData(matrix, data.concat(ecc));
  drawFormatBits(matrix);

  return matrix;
}

function createQrDataUrl(token) {
  const matrix = createQrMatrix(token);
  const pixelRatio = Math.max(2, Math.min(3, window.devicePixelRatio || 2));
  const moduleSize = Math.floor(8 * pixelRatio);
  const canvasSize = (QR_SIZE + QUIET_ZONE * 2) * moduleSize;
  const canvas = document.createElement("canvas");
  const context = canvas.getContext("2d", { alpha: false });

  canvas.width = canvasSize;
  canvas.height = canvasSize;
  context.fillStyle = "#fff";
  context.fillRect(0, 0, canvasSize, canvasSize);
  context.fillStyle = "#000";

  for (let y = 0; y < QR_SIZE; y += 1) {
    for (let x = 0; x < QR_SIZE; x += 1) {
      if (matrix[y][x].value) {
        context.fillRect(
          (x + QUIET_ZONE) * moduleSize,
          (y + QUIET_ZONE) * moduleSize,
          moduleSize,
          moduleSize,
        );
      }
    }
  }

  return canvas.toDataURL("image/png");
}

function setQr(index) {
  const item = qrItems[index];
  qrImage.src = item.src;
  qrImage.dataset.token = item.token;
}

function changeQr() {
  currentIndex = (currentIndex + 1) % qrItems.length;
  setQr(currentIndex);
}

function showHome() {
  passBackground.src = "./home.jpg";
  passStage.classList.remove("is-pass");
  passStage.classList.add("is-home");
}

function showPass() {
  passBackground.src = "./library_pass_design.jpg";
  passStage.classList.remove("is-home");
  passStage.classList.add("is-pass");
}

function lockViewport(event) {
  event.preventDefault();
}

function initPwa() {
  if ("serviceWorker" in navigator) {
    navigator.serviceWorker.register("./service-worker.js").catch(() => {});
  }
}

function initQr() {
  qrItems = Array.from({ length: QR_COUNT }, (_, index) => {
    const token = makeToken(index);
    return {
      token,
      src: createQrDataUrl(token),
    };
  });
  setQr(currentIndex);
}

document.addEventListener("gesturestart", lockViewport, { passive: false });
document.addEventListener("gesturechange", lockViewport, { passive: false });
document.addEventListener("gestureend", lockViewport, { passive: false });
document.addEventListener("touchmove", lockViewport, { passive: false });

refreshHotspot.addEventListener("click", changeQr);
backHotspot.addEventListener("click", showHome);
mobilePassHotspot.addEventListener("click", showPass);

initPwa();
initQr();
