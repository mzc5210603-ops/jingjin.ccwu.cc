/* ═══ 方块社 · 二维码工坊 —— 自研 QR 编码器 + 逻辑层 ═══ */
"use strict";

const $ = (s) => document.querySelector(s);
const $$ = (s) => document.querySelectorAll(s);
const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
window.addEventListener("error", (e) => { $("#errSink").textContent += "ERR:" + e.message + ";"; });

/* ═════════════════════════════════════════════
   QR 编码核心（byte 模式 · 版本 1–10 · L/M/Q/H）
   GF(256) Reed-Solomon + 8 掩码择优
   ═════════════════════════════════════════════ */
const QRMath = { glog: new Array(256), gexp: new Array(256) };
(function () {
  for (let i = 0; i < 8; i++) QRMath.gexp[i] = 1 << i;
  for (let i = 8; i < 256; i++) QRMath.gexp[i] = QRMath.gexp[i - 4] ^ QRMath.gexp[i - 5] ^ QRMath.gexp[i - 6] ^ QRMath.gexp[i - 8];
  for (let i = 0; i < 255; i++) QRMath.glog[QRMath.gexp[i]] = i;
})();

function QRPoly(num, shift) {
  let off = 0;
  while (off < num.length && num[off] === 0) off++;
  this.n = new Array(num.length - off + shift).fill(0);
  for (let i = off; i < num.length; i++) this.n[i - off] = num[i];
}
QRPoly.prototype.get = function (i) { return this.n[i]; };
QRPoly.prototype.len = function () { return this.n.length; };
QRPoly.prototype.mul = function (o) {
  const r = new Array(this.len() + o.len() - 1).fill(0);
  for (let i = 0; i < this.len(); i++)
    for (let j = 0; j < o.len(); j++)
      r[i + j] ^= QRMath.gexp[QRMath.glog[this.n[i]] + QRMath.glog[o.n[j]]];
  return new QRPoly(r, 0);
};
QRPoly.prototype.mod = function (o) {
  if (this.len() - o.len() < 0) return this;
  const ratio = QRMath.glog[this.n[0]] - QRMath.glog[o.n[0]];
  const num = this.n.slice();
  for (let i = 0; i < o.len(); i++)
    num[i] ^= QRMath.gexp[(QRMath.glog[o.n[i]] + ratio + 255) % 255];
  return new QRPoly(num, 0).mod(o);
};
function ecPoly(count) {
  let a = new QRPoly([1], 0);
  for (let i = 0; i < count; i++) a = a.mul(new QRPoly([1, QRMath.gexp[i]], 0));
  return a;
}

/* RS 分块表：v1–v10，顺序 [L, M, Q, H]，三元组 [块数, 总码字, 数据码字] */
const RS = [
  [[1,26,19],[1,26,16],[1,26,13],[1,26,9]],
  [[1,44,34],[1,44,28],[1,44,22],[1,44,16]],
  [[1,70,55],[1,70,44],[2,35,17],[2,35,13]],
  [[1,100,80],[2,50,32],[2,50,24],[4,25,9]],
  [[1,134,108],[2,67,43],[2,33,15,2,34,16],[2,33,11,2,34,12]],
  [[2,86,68],[4,43,27],[4,43,19],[4,43,15]],
  [[2,98,78],[4,49,31],[2,32,14,4,33,15],[4,39,13,1,40,14]],
  [[2,121,97],[2,60,38,2,61,39],[4,40,18,2,41,19],[4,40,14,2,41,15]],
  [[2,146,116],[3,58,36,2,59,37],[4,36,16,4,37,17],[4,36,12,4,37,13]],
  [[2,86,68,2,87,69],[4,69,43,1,70,44],[6,43,19,2,44,20],[6,43,15,2,44,16]],
];
const ALIGN = [[], [6,18], [6,22], [6,26], [6,30], [6,34], [6,22,38], [6,24,42], [6,26,46], [6,28,50]];
const EC_BITS = { L: 1, M: 0, Q: 3, H: 2 };
const EC_IDX = { L: 0, M: 1, Q: 2, H: 3 };

function rsBlocks(v, ec) {
  const t = RS[v - 1][EC_IDX[ec]], out = [];
  for (let i = 0; i < t.length; i += 3)
    for (let j = 0; j < t[i]; j++) out.push({ total: t[i + 1], data: t[i + 2] });
  return out;
}

function BitBuf() { this.buf = []; this.len = 0; }
BitBuf.prototype.put = function (num, length) {
  for (let i = 0; i < length; i++) this.putBit(((num >>> (length - i - 1)) & 1) === 1);
};
BitBuf.prototype.putBit = function (bit) {
  const idx = Math.floor(this.len / 8);
  if (this.buf.length <= idx) this.buf.push(0);
  if (bit) this.buf[idx] |= 0x80 >>> (this.len % 8);
  this.len++;
};

function bchDigit(d) { let e = 0; while (d !== 0) { e++; d >>>= 1; } return e; }
function bchInfo(data) {
  const G = 0x537;
  let d = data << 10;
  while (bchDigit(d) - bchDigit(G) >= 0) d ^= G << (bchDigit(d) - bchDigit(G));
  return ((data << 10) | d) ^ 0x5412;
}
function bchNumber(data) {
  const G = 0x1F25;
  let d = data << 12;
  while (bchDigit(d) - bchDigit(G) >= 0) d ^= G << (bchDigit(d) - bchDigit(G));
  return (data << 12) | d;
}
function maskFn(m, i, j) {
  switch (m) {
    case 0: return (i + j) % 2 === 0;
    case 1: return i % 2 === 0;
    case 2: return j % 3 === 0;
    case 3: return (i + j) % 3 === 0;
    case 4: return (Math.floor(i / 2) + Math.floor(j / 3)) % 2 === 0;
    case 5: return (i * j) % 2 + (i * j) % 3 === 0;
    case 6: return ((i * j) % 2 + (i * j) % 3) % 2 === 0;
    case 7: return ((i * j) % 3 + (i + j) % 2) % 2 === 0;
  }
}

/* 生成码字流：数据 + RS 纠错 + 交织 */
function makeCodewords(bytes, v, ec) {
  const blocks = rsBlocks(v, ec);
  const totalData = blocks.reduce((s, b) => s + b.data, 0);
  const bb = new BitBuf();
  bb.put(4, 4);
  bb.put(bytes.length, v <= 9 ? 8 : 16);
  for (const b of bytes) bb.put(b, 8);
  if (bb.len > totalData * 8) throw new Error("OVERFLOW");
  if (bb.len + 4 <= totalData * 8) bb.put(0, 4);
  let pad = true;
  while (bb.len < totalData * 8) { bb.put(pad ? 0xEC : 0x11, 8); pad = !pad; }

  let off = 0;
  const dBlocks = blocks.map((b) => { const d = bb.buf.slice(off, off + b.data); off += b.data; return d; });
  const ecCount = blocks[0].total - blocks[0].data;
  const gen = ecPoly(ecCount);
  const eBlocks = dBlocks.map((d) => {
    const mod = new QRPoly(d, gen.len() - 1).mod(gen);
    const ecc = new Array(gen.len() - 1).fill(0);
    for (let i = 0; i < ecc.length; i++) {
      const mi = i + mod.len() - ecc.length;
      ecc[i] = mi >= 0 && mi < mod.len() ? mod.get(mi) : 0;
    }
    return ecc;
  });
  const out = [];
  const maxD = Math.max.apply(null, dBlocks.map((b) => b.length));
  for (let i = 0; i < maxD; i++) for (const b of dBlocks) if (i < b.length) out.push(b[i]);
  for (let i = 0; i < ecCount; i++) for (const b of eBlocks) out.push(b[i]);
  return out;
}

/* 搭矩阵（含掩码与格式信息） */
function buildMatrix(v, ec, out, mask, test) {
  const n = 4 * v + 17;
  const M = Array.from({ length: n }, () => new Array(n).fill(null));
  const probe = (r, c) => {
    for (let i = -1; i <= 7; i++) {
      if (r + i < 0 || n <= r + i) continue;
      for (let j = -1; j <= 7; j++) {
        if (c + j < 0 || n <= c + j) continue;
        M[r + i][c + j] =
          (i >= 0 && i <= 6 && (j === 0 || j === 6)) ||
          (j >= 0 && j <= 6 && (i === 0 || i === 6)) ||
          (i >= 2 && i <= 4 && j >= 2 && j <= 4);
      }
    }
  };
  probe(0, 0); probe(0, n - 7); probe(n - 7, 0);
  for (let i = 8; i < n - 8; i++) {
    if (M[i][6] === null) M[i][6] = i % 2 === 0;
    if (M[6][i] === null) M[6][i] = i % 2 === 0;
  }
  const pos = ALIGN[v - 1];
  for (const r of pos) for (const c of pos) {
    if (M[r][c] !== null) continue;
    for (let i = -2; i <= 2; i++) for (let j = -2; j <= 2; j++)
      M[r + i][c + j] = i === -2 || i === 2 || j === -2 || j === 2 || (i === 0 && j === 0);
  }
  if (v >= 7) {
    const bits = bchNumber(v);
    for (let i = 0; i < 18; i++) {
      const bit = ((bits >> i) & 1) === 1;
      M[Math.floor(i / 3)][i % 3 + n - 11] = bit;
      M[i % 3 + n - 11][Math.floor(i / 3)] = bit;
    }
  }
  const data = (EC_BITS[ec] << 3) | mask;
  const bits = bchInfo(data);
  for (let i = 0; i < 15; i++) {
    const mod = !test && ((bits >> i) & 1) === 1;
    if (i < 6) M[i][8] = mod;
    else if (i < 8) M[i + 1][8] = mod;
    else M[n - 15 + i][8] = mod;
  }
  for (let i = 0; i < 15; i++) {
    const mod = !test && ((bits >> i) & 1) === 1;
    if (i < 8) M[8][i] = mod;
    else if (i < 9) M[8][i + 1] = mod;
    else M[8][i - 15 + n] = mod;
  }
  M[n - 8][8] = !test;
  let inc = -1, row = n - 1, bitIdx = 7, byteIdx = 0;
  for (let col = n - 1; col > 0; col -= 2) {
    if (col === 6) col--;
    for (;;) {
      for (let c = 0; c < 2; c++) {
        if (M[row][col - c] === null) {
          let dark = false;
          if (byteIdx < out.length) dark = ((out[byteIdx] >>> bitIdx) & 1) === 1;
          if (maskFn(mask, row, col - c)) dark = !dark;
          M[row][col - c] = dark;
          bitIdx--;
          if (bitIdx === -1) { byteIdx++; bitIdx = 7; }
        }
      }
      row += inc;
      if (row < 0 || n <= row) { row -= inc; inc = -inc; break; }
    }
  }
  return M;
}

/* 恶化值评分（择掩码用） */
function lostPoint(M) {
  const n = M.length;
  let lost = 0;
  for (let row = 0; row < n; row++) for (let col = 0; col < n; col++) {
    let same = 0;
    const dark = M[row][col];
    for (let r = -1; r <= 1; r++) {
      if (row + r < 0 || n <= row + r) continue;
      for (let c = -1; c <= 1; c++) {
        if (col + c < 0 || n <= col + c || (r === 0 && c === 0)) continue;
        if (dark === M[row + r][col + c]) same++;
      }
    }
    if (same > 5) lost += 3 + same - 5;
  }
  for (let row = 0; row < n - 1; row++) for (let col = 0; col < n - 1; col++) {
    let cnt = 0;
    if (M[row][col]) cnt++;
    if (M[row + 1][col]) cnt++;
    if (M[row][col + 1]) cnt++;
    if (M[row + 1][col + 1]) cnt++;
    if (cnt === 0 || cnt === 4) lost += 3;
  }
  for (let row = 0; row < n; row++) for (let col = 0; col < n - 6; col++) {
    if (M[row][col] && !M[row][col + 1] && M[row][col + 2] && M[row][col + 3] && M[row][col + 4] && !M[row][col + 5] && M[row][col + 6]) lost += 40;
  }
  for (let col = 0; col < n; col++) for (let row = 0; row < n - 6; row++) {
    if (M[row][col] && !M[row + 1][col] && M[row + 2][col] && M[row + 3][col] && M[row + 4][col] && !M[row + 5][col] && M[row + 6][col]) lost += 40;
  }
  let darkCnt = 0;
  for (let col = 0; col < n; col++) for (let row = 0; row < n; row++) if (M[row][col]) darkCnt++;
  lost += Math.abs(100 * darkCnt / n / n - 50) / 5 * 10;
  return lost;
}

/* 入口：字节 → 模块矩阵 */
function qrEncode(text, ec) {
  const bytes = Array.from(new TextEncoder().encode(text));
  let v = 0, out = null;
  for (let tryV = 1; tryV <= 10; tryV++) {
    const blocks = rsBlocks(tryV, ec);
    const cap = blocks.reduce((s, b) => s + b.data, 0);
    const lenBits = tryV <= 9 ? 8 : 16;
    if (4 + lenBits + bytes.length * 8 <= cap * 8) {
      v = tryV;
      out = makeCodewords(bytes, v, ec);
      break;
    }
  }
  if (!out) throw new Error("OVERFLOW");
  let best = 0, bestScore = Infinity;
  for (let m = 0; m < 8; m++) {
    const s = lostPoint(buildMatrix(v, ec, out, m, true));
    if (s < bestScore) { bestScore = s; best = m; }
  }
  return { m: buildMatrix(v, ec, out, best, false), version: v, mask: best };
}

/* ═══ 画布渲染 ═══ */
let logoImg = null;
function renderQR(M, canvas, size, opts) {
  const n = M.length, quiet = 4, total = n + quiet * 2;
  const scale = Math.max(2, Math.floor(size / total));
  const px = scale * total;
  canvas.width = px; canvas.height = px;
  const ctx = canvas.getContext("2d");
  ctx.clearRect(0, 0, px, px);
  if (!opts.trans) {
    ctx.fillStyle = opts.light;
    ctx.fillRect(0, 0, px, px);
  }
  ctx.fillStyle = opts.dark;
  const isFinder = (r, c) => (r < 7 && c < 7) || (r < 7 && c >= n - 7) || (r >= n - 7 && c < 7);
  for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) {
    if (!M[r][c]) continue;
    const x = (c + quiet) * scale, y = (r + quiet) * scale;
    if (opts.style === "dot" && !isFinder(r, c)) {
      ctx.beginPath();
      ctx.arc(x + scale / 2, y + scale / 2, scale / 2 - scale * 0.12, 0, Math.PI * 2);
      ctx.fill();
    } else {
      ctx.fillRect(x, y, scale, scale);
    }
  }
  if (logoImg) {
    const side = Math.floor(px * 0.22);
    const cx = (px - side) / 2;
    ctx.fillStyle = opts.trans ? "#ffffff" : opts.light;
    ctx.fillRect(cx - 6, cx - 6, side + 12, side + 12);
    try { ctx.drawImage(logoImg, cx, cx, side, side); } catch {}
  }
}

/* ═══════════ 码型表单 ═══════════ */
const TYPES = {
  text: { name: "文本", fields: [{ k: "t", l: "内容", type: "textarea", ph: "写点什么放进二维码里…" }] },
  url: { name: "网址", fields: [{ k: "u", l: "链接", type: "text", ph: "https://…" }] },
  wifi: {
    name: "Wi-Fi", fields: [
      { k: "s", l: "名称 SSID", type: "text", ph: "MyWiFi" },
      { k: "p", l: "密码", type: "text", ph: "…" },
      { k: "e", l: "加密", type: "select", opts: ["WPA/WPA2", "WEP", "无加密"] },
    ],
  },
  vcard: {
    name: "名片", fields: [
      { k: "n", l: "姓名", type: "text", ph: "李雷" },
      { k: "t", l: "电话", type: "tel", ph: "13800000000" },
      { k: "m", l: "邮箱", type: "email", ph: "li@lei.com" },
      { k: "o", l: "单位", type: "text", ph: "方块社" },
      { k: "w", l: "网址", type: "text", ph: "https://…" },
    ],
  },
  tel: { name: "电话", fields: [{ k: "t", l: "号码", type: "tel", ph: "13800000000" }] },
  sms: {
    name: "短信", fields: [
      { k: "t", l: "号码", type: "tel", ph: "13800000000" },
      { k: "b", l: "内容", type: "text", ph: "（可留空）" },
    ],
  },
  mail: {
    name: "邮件", fields: [
      { k: "a", l: "地址", type: "email", ph: "someone@example.com" },
      { k: "s", l: "主题", type: "text", ph: "（可留空）" },
    ],
  },
  geo: {
    name: "位置", fields: [
      { k: "a", l: "纬度", type: "text", ph: "39.9042" },
      { k: "o", l: "经度", type: "text", ph: "116.4074" },
    ],
  },
};
let curType = "text";
const formData = {};

function renderForm() {
  const t = TYPES[curType];
  const f = $("#typeForm");
  f.innerHTML = "";
  t.fields.forEach((fd) => {
    const row = document.createElement("div");
    row.className = "row";
    const key = curType + "." + fd.k;
    if (fd.type === "select") {
      row.innerHTML = "<label class='fl'>" + esc(fd.l) + "</label><select data-k='" + key + "'>" +
        fd.opts.map((o) => "<option>" + esc(o) + "</option>").join("") + "</select>";
    } else if (fd.type === "textarea") {
      row.innerHTML = "<textarea data-k='" + key + "' placeholder='" + esc(fd.ph) + "'>" + esc(formData[key] || "") + "</textarea>";
    } else {
      row.innerHTML = "<label class='fl'>" + esc(fd.l) + "</label><input type='" + fd.type + "' data-k='" + key + "' placeholder='" + esc(fd.ph) + "' value='" + esc(formData[key] || "") + "'>";
    }
    f.appendChild(row);
  });
  $("#stMode").textContent = t.name;
}
$("#typeGrid").addEventListener("click", (e) => {
  const li = e.target.closest("li");
  if (!li) return;
  $$("#typeGrid li").forEach((x) => x.classList.toggle("on", x === li));
  curType = li.dataset.ty;
  renderForm();
});
renderForm();

/* 组装有效载荷 */
function wifiEsc(s) { return s.replace(/([\\;,:"])/g, "\\$1"); }
function buildPayload() {
  const v = (k) => formData[curType + "." + k] || "";
  switch (curType) {
    case "text": return v("t");
    case "url": { let u = v("u").trim(); if (u && !/^[a-z][a-z0-9+.-]*:/i.test(u)) u = "https://" + u; return u; }
    case "wifi": {
      const e = v("e") === "无加密" ? "nopass" : v("e") === "WEP" ? "WEP" : "WPA";
      return "WIFI:T:" + e + ";S:" + wifiEsc(v("s")) + (e !== "nopass" ? ";P:" + wifiEsc(v("p")) : "") + ";;";
    }
    case "vcard": {
      const n = v("n").trim();
      if (!n) return "";
      return "BEGIN:VCARD\nVERSION:3.0\nFN:" + n + "\nN:" + n +
        (v("t") ? "\nTEL:" + v("t") : "") +
        (v("m") ? "\nEMAIL:" + v("m") : "") +
        (v("o") ? "\nORG:" + v("o") : "") +
        (v("w") ? "\nURL:" + v("w") : "") + "\nEND:VCARD";
    }
    case "tel": return "tel:" + v("t").replace(/[^\d+]/g, "");
    case "sms": return "SMSTO:" + v("t").replace(/[^\d+]/g, "") + ":" + v("b");
    case "mail": return "mailto:" + v("a") + (v("s") ? "?subject=" + encodeURIComponent(v("s")) : "");
    case "geo": return "geo:" + v("a").trim() + "," + v("o").trim();
  }
}

/* ═══ 生成 ═══ */
let lastMatrix = null;
function generate() {
  const payload = buildPayload();
  const note = $("#stageNote");
  if (!payload.trim()) {
    note.textContent = "内容还是空的 —— 填点什么再生成。";
    $("#stInfo").textContent = "空载荷";
    return;
  }
  const ec = document.querySelector('input[name="ec"]:checked').value;
  try {
    const { m, version, mask } = qrEncode(payload, ec);
    lastMatrix = m;
    const opts = readOpts();
    renderQR(m, $("#qrCanvas"), 300, opts);
    const n = m.length;
    const bytes = new TextEncoder().encode(payload).length;
    note.innerHTML = "版本 <b>" + version + "</b>（" + n + "×" + n + " 模块）· 纠错 <b>" + ec +
      "</b> · 掩码 <b>" + mask + "</b><br>载荷 " + bytes + " 字节 · " + esc(TYPES[curType].name);
    $("#stInfo").textContent = "v" + version + " · EC" + ec + " · mask" + mask;
    $("#hdStat").textContent = "v" + version;
    addHistory(payload, TYPES[curType].name);
  } catch (err) {
    note.textContent = err.message === "OVERFLOW"
      ? "内容太长，超出 v10 容量（约 " + (ec === "L" ? 271 : ec === "M" ? 213 : ec === "Q" ? 151 : 119) + " 字节）—— 删减或降纠错等级。"
      : "生成失败：" + err.message;
    $("#stInfo").textContent = "生成失败";
  }
}
function readOpts() {
  return {
    style: document.querySelector('input[name="dotStyle"]:checked').value,
    dark: $("#cDark").value,
    light: $("#cLight").value,
    trans: $("#cTrans").checked,
  };
}
$("#goBtn").addEventListener("click", generate);
$("#typeForm").addEventListener("input", (e) => {
  if (e.target.dataset.k) formData[e.target.dataset.k] = e.target.value;
});
$("#typeForm").addEventListener("change", (e) => {
  if (e.target.dataset.k) formData[e.target.dataset.k] = e.target.value;
});

/* 选项变化即时重绘 */
["#cDark", "#cLight", "#cTrans"].forEach((id) =>
  $(id).addEventListener("input", () => { if (lastMatrix) renderQR(lastMatrix, $("#qrCanvas"), 300, readOpts()); }));
$$('input[name="dotStyle"]').forEach((r) =>
  r.addEventListener("change", () => { if (lastMatrix) renderQR(lastMatrix, $("#qrCanvas"), 300, readOpts()); }));

/* Logo 贴图 */
$("#logoFile").addEventListener("change", (e) => {
  const f = e.target.files[0];
  if (!f) return;
  const img = new Image();
  img.onload = () => {
    logoImg = img;
    if (lastMatrix) renderQR(lastMatrix, $("#qrCanvas"), 300, readOpts());
    $("#stInfo").textContent = "已贴 logo（建议纠错 H）";
  };
  img.src = URL.createObjectURL(f);
});
$("#logoClear").addEventListener("click", () => {
  logoImg = null;
  if (lastMatrix) renderQR(lastMatrix, $("#qrCanvas"), 300, readOpts());
  $("#stInfo").textContent = "logo 已取下";
});

/* 下载 */
function download(size) {
  if (!lastMatrix) { $("#stInfo").textContent = "先生成一张再下载"; return; }
  const c = document.createElement("canvas");
  renderQR(lastMatrix, c, size, readOpts());
  const a = document.createElement("a");
  a.href = c.toDataURL("image/png");
  a.download = "qr-" + size + "px.png";
  document.body.appendChild(a); a.click(); a.remove();
  $("#stInfo").textContent = "已导出 " + size + "px PNG";
}
$("#dlS").addEventListener("click", () => download(300));
$("#dlM").addEventListener("click", () => download(600));
$("#dlL").addEventListener("click", () => download(1200));

/* ═══ 近作（localStorage） ═══ */
const HIST_LS = "qr_bauhaus_hist_v1";
let hist = [];
try { hist = JSON.parse(localStorage.getItem(HIST_LS) || "[]"); } catch {}
function renderHist() {
  const ul = $("#histList");
  ul.innerHTML = "";
  if (!hist.length) {
    ul.innerHTML = "<li class='empty'>还没有生成记录。生成后自动留档（仅存文本，存在本机）。</li>";
    return;
  }
  hist.forEach((h) => {
    const li = document.createElement("li");
    li.innerHTML = "<span class='h-ty'>" + esc(h.ty) + "</span><span class='h-tx'>" + esc(h.text) +
      "</span><span class='h-tm'>" + esc(h.at) + "</span>";
    li.addEventListener("click", () => {
      $("#q").value = "";
      formData["text.t"] = h.text;
      $$("#typeGrid li").forEach((x) => x.classList.toggle("on", x.dataset.ty === "text"));
      curType = "text";
      renderForm();
      formData["text.t"] = h.text;
      generate();
    });
    ul.appendChild(li);
  });
}
function addHistory(text, ty) {
  const n = new Date();
  hist.unshift({ text, ty, at: [n.getHours(), n.getMinutes()].map((x) => String(x).padStart(2, "0")).join(":") });
  hist = hist.slice(0, 8);
  try { localStorage.setItem(HIST_LS, JSON.stringify(hist)); } catch {}
  renderHist();
}
renderHist();

/* 初始演示：默认文本内容生成一张 */
formData["text.t"] = "方块社 · 二维码工坊 No.27\nhttps://example.com";
renderForm();
generate();
