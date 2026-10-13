from pathlib import Path
import csv, re, json, hashlib
import pdfplumber

root = Path(__file__).resolve().parent.parent
stem = 'time_inhomogeneous_riffle_shuffle_lean_paper'
tex = (root / (stem+'.tex')).read_text(encoding='utf-8')
rows = list(csv.DictReader((root/'time_inhomogeneous_riffle_shuffle_lean_sources.tsv').open(encoding='utf-8'),delimiter='\t'))
missing = []
source_hashes = {}
for row in rows:
    path = root / row['Lean_source']
    source = path.read_text(encoding='utf-8-sig')
    source_hashes[row['Lean_source']] = hashlib.sha256(path.read_bytes()).hexdigest()
    for full in row['Lean_declarations'].split(';'):
        name = full.strip().split('.')[-1]
        if not re.search(r'\b(?:theorem|lemma|def|abbrev|structure|class)\s+(?:[\w.]+\.)?'+re.escape(name)+r'(?![\w])',source):
            missing.append({'file':row['Lean_source'],'declaration':full.strip()})
log = (root/'tmp/paper_build'/(stem+'.log')).read_text(encoding='utf-8',errors='replace')
warnings = [line for line in log.splitlines() if any(s in line for s in ['Overfull','Underfull','LaTeX Warning','Package hyperref Warning','Undefined control sequence'])]
pdf = root/'tmp/paper_build'/(stem+'.pdf')
pages = []
with pdfplumber.open(pdf) as document:
    for i,p in enumerate(document.pages,1):
        chars = [c for c in p.chars if c.get('text','').strip()]
        # The centered folio at y=741--752 is intentionally below the text area.
        body = [c for c in chars if not (c['text'].isdigit() and abs((c['x0']+c['x1'])/2-p.width/2)<12 and 735<c['top']<755)]
        outside = [c for c in body if c['x0']<65 or c['x1']>p.width-64 or c['top']<55 or c['bottom']>p.height-40]
        pages.append({'page':i,'characters':len(chars),'outside_safe_page_area':len(outside),
                      'outside_samples':[{k:c[k] for k in ['text','x0','x1','top','bottom']} for c in outside[:12]]})
report={'tex_sha256':hashlib.sha256((root/(stem+'.tex')).read_bytes()).hexdigest(),
        'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest(),
        'source_map_rows':len(rows),'source_file_hashes':source_hashes,
        'missing_declarations':missing,'latex_warnings':warnings,'pages':pages}
(root/'tmp/paper_final_audit.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
print(json.dumps({'source_map_rows':len(rows),'mapped_source_files':len(source_hashes),
                  'missing_declarations':missing,'latex_warnings':warnings,
                  'page_count':len(pages),'empty_pages':[p['page'] for p in pages if p['characters']<20],
                  'page_area_exceptions':[p for p in pages if p['outside_safe_page_area']]},indent=2))
