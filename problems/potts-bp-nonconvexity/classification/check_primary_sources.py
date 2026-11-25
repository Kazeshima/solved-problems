"""Fetch versioned primary texts and record page-level keyword checks, without redistributing PDFs."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib, io, json, re, subprocess, sys
from pathlib import Path
from pypdf import PdfReader

root=Path(__file__).resolve().parent
ids=["2411.06541v2","2611.32635v1","1804.03514v1","2011.05638v3","2608.25491v1","2603.17858v2","2610.42059v1"]
terms={"convex hull":r"convex hull","image of product measures":r"image of (?:the (?:set|class) of )?(?:all )?product",
       "Question 4":r"Question\s*4\b","convex potential":r"convex potential","Weitz":r"Weitz",
       "log-convex":r"log[- ]?convex","arXiv target":r"2411\.06541|LMP2[45]","surjectivity":r"surjectiv",
       "independent messages":r"independent (?:neighbo[u]?rs|messages)"}
def one(i):
    url="https://arxiv.org/pdf/"+i
    p=subprocess.run(["curl","-fLsS","--connect-timeout","8","--retry","1","--max-time","45","-A","Potts classification review",url],capture_output=True)
    row={"date":datetime.now(timezone.utc).isoformat(),"url":url,"exit":p.returncode}
    if p.returncode:return row
    row["sha256"]=hashlib.sha256(p.stdout).hexdigest()
    try:
        r=PdfReader(io.BytesIO(p.stdout)); row["pages"]=len(r.pages)
        text=[re.sub(r"\s+"," ",pg.extract_text() or "") for pg in r.pages]
        row["term_pages"]={term:[k for k,s in enumerate(text,1) if re.search(pat,s,re.I)] for term,pat in terms.items()}
        row["title_page"]=text[0][:240]
    except Exception as e:row["parse_error"]=str(e)
    return row
with ThreadPoolExecutor(max_workers=4) as ex: rows=list(ex.map(one,ids))
(root/"results"/"primary-texts.json").write_text(json.dumps(rows,indent=2,ensure_ascii=False)+"\n",encoding="utf8")
print([(r["url"],r.get("pages"),r["exit"]) for r in rows])
