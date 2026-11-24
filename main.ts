import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const ST = 1000000;
const OU = 65536;
const SK = 256;
const CK = 64;
const MW = 256;

const SPEC: Record<number, [number, number, number]> = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2],
  5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3], 16: [0, 2, 1], 17: [0, 2, 1],
  18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1], 21: [0, 2, 1], 22: [0, 2, 1],
  23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1], 26: [0, 2, 1], 27: [0, 1, 1],
  28: [0, 2, 1], 29: [0, 2, 1], 30: [0, 2, 1], 32: [0, 2, 1], 33: [0, 2, 1],
  34: [0, 2, 1], 48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0], 51: [2, 0, 0],
  52: [0, 0, 0], 64: [0, 1, 1], 65: [0, 2, 0], 80: [0, 1, 0], 81: [0, 1, 0],
  82: [0, 0, 1], 83: [0, 1, 0],
};

function run1(prog: Buffer, input: Buffer): { bytes: Buffer; code: number } {
  const s = new Int32Array(SK);
  const c = new Int32Array(CK);
  const m = new Int32Array(MW);
  const o = new Uint8Array(OU);
  const n = prog.length;
  let sp = 0;
  let cp = 0;
  let ip = 0;
  let pc = 0;
  let olen = 0;
  let steps = 0;
  const fin = (code: number) => ({ bytes: Buffer.from(o.subarray(0, olen)), code });
  for (;;) {
    if (steps >= ST) return fin(10);
    if (pc < 0 || pc >= n) return fin(9);
    const op = prog[pc];
    const spec = SPEC[op];
    if (spec === undefined) return fin(5);
    const immLen = spec[0];
    if (pc + immLen >= n) return fin(9);
    steps += 1;
    if (sp < spec[1]) return fin(2);
    if (sp - spec[1] + spec[2] > SK) return fin(3);
    const next = pc + 1 + immLen;
    pc = next;
    switch (op) {
      case 0x00:
        return fin(0);
      case 0x01:
        s[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02:
        s[sp++] =
          prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp -= 1;
        break;
      case 0x04:
        s[sp] = s[sp - 1];
        sp += 1;
        break;
      case 0x05: {
        const tmp = s[sp - 1];
        s[sp - 1] = s[sp - 2];
        s[sp - 2] = tmp;
        break;
      }
      case 0x06:
        s[sp] = s[sp - 2];
        sp += 1;
        break;
      case 0x07: {
        const tmp = s[sp - 3];
        s[sp - 3] = s[sp - 2];
        s[sp - 2] = s[sp - 1];
        s[sp - 1] = tmp;
        break;
      }
      case 0x17:
        s[sp - 1] = -s[sp - 1] | 0;
        break;
      case 0x1b:
        s[sp - 1] = ~s[sp - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22: {
        const b = s[sp - 1];
        const a = s[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return fin(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return fin(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return fin(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return fin(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        s[sp++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = s[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === CK) return fin(7);
        c[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return fin(8);
        pc = c[--cp];
        break;
      case 0x40: {
        const addr = s[sp - 1];
        if (addr < 0 || addr >= MW) return fin(6);
        s[sp - 1] = m[addr];
        break;
      }
      case 0x41: {
        const addr = s[sp - 1];
        const v = s[sp - 2];
        if (addr < 0 || addr >= MW) return fin(6);
        sp -= 2;
        m[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = Buffer.from(String(s[sp - 1]));
        if (olen + bytes.length > OU) return fin(11);
        sp -= 1;
        o.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OU) return fin(11);
        o[olen++] = s[--sp] & 255;
        break;
      case 0x52:
        s[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return fin(s[--sp] & 255);
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
const rd = (f: string) => {
  try {
    return readFileSync(f);
  } catch {
    return Buffer.alloc(0);
  }
};
for (const id of readdirSync(IN_DIR).sort()) {
  const res = run1(rd(join(IN_DIR, id, "program.bin")), rd(join(IN_DIR, id, "input.bin")));
  const od = join(OUT_DIR, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, "stdout.bin"), res.bytes);
  writeFileSync(join(od, "exit.txt"), String(res.code) + "\n");
}
