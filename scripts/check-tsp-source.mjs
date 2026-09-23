// Scan Lean source after removing nested comments and quoted strings.
import fs from 'node:fs';
function codeOnly(text) {
  let out = '', depth = 0, quote = false;
  for (let i = 0; i < text.length; i++) {
    const pair = text.slice(i, i + 2), c = text[i];
    if (depth) {
      if (pair === '/-') { depth++; i++; }
      else if (pair === '-/') { depth--; i++; }
      else if (c === '\n') out += '\n';
    } else if (quote) {
      if (c === '\\') i++;
      else if (c === '"') quote = false;
      else if (c === '\n') out += '\n';
    } else if (pair === '/-') { depth = 1; out += ' '; i++; }
    else if (pair === '--') {
      while (i < text.length && text[i] !== '\n') i++;
      out += '\n';
    } else if (c === '"') { quote = true; out += ' '; }
    else out += c;
  }
  if (depth || quote) throw new Error('Unterminated comment or string');
  return out;
}
let count = 0;
function check(directory) {
  for (const item of fs.readdirSync(directory, {withFileTypes: true})) {
    const file = directory + '/' + item.name;
    if (item.isDirectory()) check(file);
    else if (file.endsWith('.lean')) {
      const code = codeOnly(fs.readFileSync(file, 'utf8'));
      if (/\b(sorry|admit|axiom)\b/.test(code)) throw new Error('Admission token in ' + file);
      count++;
    }
  }
}
check('TSPGap');
for (const file of ['TSPGap.lean', 'TSPGapChecks.lean']) {
  if (/\b(sorry|admit|axiom)\b/.test(codeOnly(fs.readFileSync(file, 'utf8')))) {
    throw new Error('Admission token in ' + file);
  }
}

console.log('PASS: no source admissions in ' + count + ' TSP library modules and both public entry files.');

