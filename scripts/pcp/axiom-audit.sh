#!/usr/bin/env bash
set -euo pipefail
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO_ROOT"
lake --no-cache --no-build build PCP >/dev/null
AUDIT_OUTPUT="$(mktemp)"
trap 'rm -f "$AUDIT_OUTPUT"' EXIT
lake env lean scripts/pcp/audit.lean > "$AUDIT_OUTPUT"
python3 - "$AUDIT_OUTPUT" <<'PY'
from pathlib import Path
import sys
output = Path(sys.argv[1]).read_text()
seen = {line[7:] for line in output.splitlines() if line.startswith('MODULE ')}
for line in output.splitlines():
    if not line.startswith('MODULE '):
        print(line)
# Every PCP source file must be reachable from the root import, so none escapes the audit.
expected = {'PCP'} | {'.'.join(p.with_suffix('').parts) for p in Path('PCP').rglob('*.lean')}
vendor = {'.'.join(p.relative_to('vendor').with_suffix('').parts)
          for p in Path('vendor').rglob('*.lean')}
seen_pcp = {m for m in seen if m == 'PCP' or m.startswith('PCP.')}
seen_vendor = seen - seen_pcp
missing, extra = expected - seen_pcp, seen_pcp - expected
unknown = seen_vendor - vendor
if missing or extra or unknown:
    raise SystemExit(f'Module coverage mismatch: missing={sorted(missing)}, '
                     f'extra={sorted(extra)}, unknown vendor={sorted(unknown)}')
print(f'All {len(expected)} PCP modules and the {len(seen_vendor)} imported vendored '
      'modules are covered by the root import.')
PY
