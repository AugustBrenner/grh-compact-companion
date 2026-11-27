#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -d /Library/TeX/texbin ]; then
    PATH="/Library/TeX/texbin:$PATH"
    export PATH
fi
rm -f paper_c.aux paper_c.out paper_c.toc build_report.json
python3 -I verify_paper_c.py > verification_stdout.json
pass=0
previous=''
converged=0
while [ "$pass" -lt 5 ]; do
    pass=$((pass+1))
    pdflatex -interaction=nonstopmode -halt-on-error paper_c.tex > "build-pass-$pass.txt"
    current=$(shasum -a 256 paper_c.aux paper_c.out)
    if [ "$pass" -ge 2 ] && [ "$current" = "$previous" ]; then
        converged=1
        break
    fi
    previous=$current
done
[ "$converged" -eq 1 ] || { echo 'Auxiliary files did not converge' >&2; exit 1; }
PAPER_C_BUILD_PASSES="$pass" python3 -I - <<'PY'
from pathlib import Path
import re, json, os, subprocess
log = Path('paper_c.log').read_text(encoding='latin-1')
assert not re.search(r'(^!|undefined|Rerun to get|Label\(s\) may have changed|LaTeX Warning:|Package [^:\n]+ Warning:|Class [^:\n]+ Warning:|pdfTeX warning|Font Warning)', log, re.M | re.I), "LaTeX errors, warnings, or undefined refs"
over_h = [float(x) for x in re.findall(r'Overfull \\hbox \(([0-9.]+)pt too wide\)', log)]
over_v = [float(x) for x in re.findall(r'Overfull \\vbox \(([0-9.]+)pt too high\)', log)]
under_h = [int(x) for x in re.findall(r'Underfull \\hbox \(badness (\d+)\)', log)]
under_v = [int(x) for x in re.findall(r'Underfull \\vbox \(badness (\d+)\)', log)]
assert not over_h, f"Overfull hboxes: {over_h}"
assert not over_v, f"Overfull vboxes: {over_v}"
assert not under_h, f"Underfull hboxes: {under_h}"
assert not under_v, f"Underfull vboxes: {under_v}"
pages = re.search(r'Output written on paper_c.pdf \((\d+) pages', log)
assert pages
report = {
    'pages': int(pages[1]),
    'errors': 0,
    'undefined_references': 0,
    'undefined_citations': 0,
    'overfull_hboxes_pt': over_h,
    'overfull_vboxes_pt': over_v,
    'underfull_hboxes_badness': under_h,
    'underfull_vboxes_badness': under_v,
    'aux_converged': True,
    'passes': int(os.environ['PAPER_C_BUILD_PASSES']),
}
subprocess.run(['pdftotext', '-layout', 'paper_c.pdf', 'paper_c.txt'], check=True)
Path('build_report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
PY
