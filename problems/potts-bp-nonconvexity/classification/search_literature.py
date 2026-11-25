"""Repeat the public, read-only bibliographic and repository searches for the classification."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from pathlib import Path
import hashlib, html, json, re, subprocess, sys
from urllib.parse import quote
import xml.etree.ElementTree as ET

Q="antiferromagnetic Potts belief propagation image convexity"
A="normalized Hadamard product probability simplex convex"
T="Counterexamples to a Weitz-Style Reduction for Multispin Systems"
E=lambda s:quote(s,safe="")
urls={
"arXiv subject query":"https://export.arxiv.org/api/query?search_query="+E('all:"antiferromagnetic Potts" AND (all:"convexity" OR all:"belief propagation")')+"&max_results=30",
"arXiv v2":"https://arxiv.org/abs/2411.06541v2",
"Crossref Potts":"https://api.crossref.org/works?rows=8&select=title,DOI&query.bibliographic="+E(Q),
"Crossref equivalent geometry":"https://api.crossref.org/works?rows=8&select=title,DOI&query.bibliographic="+E(A),
"OpenAlex classification":"https://api.openalex.org/works?per_page=12&search="+E(Q),
"OpenAlex cited by":"https://api.openalex.org/works?per_page=100&select=id,title,doi,publication_date&filter=cites:W4404391313",
"OpenAlex original and references":"https://api.openalex.org/works/W4404391313?select=id,title,doi,referenced_works,cited_by_count",
"Semantic Scholar cited by":"https://api.semanticscholar.org/graph/v1/paper/ARXIV:2411.06541/citations?limit=100&fields=title,year,url",
"Semantic Scholar new terms":"https://api.semanticscholar.org/graph/v1/paper/search?limit=8&fields=title,year,url&query="+E(Q),
"DataCite query":"https://api.datacite.org/dois?page[size]=8&query="+E('titles.title:("Potts" AND "belief propagation" AND "convexity")'),
"DBLP publications":"https://dblp.org/search/publ/api?format=json&h=10&q="+E("Potts convexity belief propagation"),
"Google Scholar":"https://scholar.google.com/scholar?q="+E('"Potts" "belief propagation" "convexity" simplex'),
"zbMATH":"https://api.zbmath.org/v1/document/_search?results_per_page=10&search_string="+E('ti:"Potts" & ti:"convexity"'),
"MathSciNet":"https://mathscinet.ams.org/mathscinet/search/publications.html?pg1=ALLF&s1="+E(Q),
"Math-Net.Ru":"https://www.mathnet.ru/php/search.phtml?wshow=search&option_lang=eng&words="+E(Q),
"Scopus":"https://www.scopus.com/results/results.uri?src=s&s="+E('TITLE-ABS-KEY("Potts" AND "belief propagation" AND convexity)'),
"Web of Science":"https://www.webofscience.com/wos/woscc/basic-search",
"Dimensions":"https://app.dimensions.ai/discover/publication?search_text="+E(Q),
"Zenodo":"https://zenodo.org/api/records?size=8&q="+E('"Potts" AND "belief propagation" AND "convexity"'),
"Figshare":"https://api.figshare.com/v2/articles/search",
"OSF":"https://api.osf.io/v2/preprints/?filter[title]="+E("Potts belief propagation"),
"HAL":"https://api.archives-ouvertes.fr/search/?wt=json&fl=title_s,uri_s&rows=10&q="+E('title_t:Potts AND text:"belief propagation" AND text:convexity'),
"SSRN":"https://papers.ssrn.com/sol3/results.cfm?txtKey_Words="+E(Q),
"OpenReview":"https://api2.openreview.net/notes/search?limit=8&term="+E(Q),
"GitHub repo":"https://api.github.com/search/repositories?per_page=10&q="+E("Potts belief propagation convexity"),
"GitHub discussion":"https://api.github.com/search/issues?per_page=10&q="+E('"Potts" "convexity" "belief propagation"'),
"GitLab":"https://gitlab.com/api/v4/projects?per_page=10&search=PottsBP",
"Bitbucket":"https://api.bitbucket.org/2.0/repositories?q="+E('name ~ "PottsBP"'),
"Codeberg":"https://codeberg.org/api/v1/repos/search?q=PottsBP&limit=10",
"Hugging Face":"https://huggingface.co/api/datasets?search="+E("Potts belief propagation")+"&limit=10",
"MathOverflow":"https://api.stackexchange.com/2.3/search/advanced?site=mathoverflow&q="+E("Potts convexity belief propagation"),
"Mathematics Stack Exchange":"https://api.stackexchange.com/2.3/search/advanced?site=math&q="+E("Potts belief propagation convexity"),
"Open Math Atlas":"https://open-math-atlas.com/explorer",
"MathDB":"https://mathdb.com/database?tag=product-measures",
"ProbXiv":"https://probxiv.com/",
"EulerSolve research catalog":"https://eulersolve.org/papers/",
"Hexagon form":"https://hexagonmath.org/search?q="+E("Potts belief propagation"),
"aiXiv form":"https://aixiv.online/search?q="+E("Potts convexity"),
"Evidence Press related counterexample":"https://evidencepress.org/releases/potts-censoring-counterexample/",
"AI Proof Watch":"https://aiproofwatch.com/",
"OpenAI math catalog":"https://raw.githubusercontent.com/openai/math/main/overview.tex",
"Mathlib documentation":"https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html",
"Open Problems Catalog Q4813 followup":"https://api.github.com/repos/10m-u/open-problems-catalog/pulls/7",
"Kazeshima prior note":"https://raw.githubusercontent.com/Kazeshima/solved-problems/22864a3858ae02109d70c5743de1ec145113cc0b/problems/potts-bp-nonconvexity/paper.tex",
"Liu publications":"https://kuikuiliu.github.io/publications/",
"Mani publications":"https://www.mit.edu/~nmani/",
"Pernice publications":"https://sites.google.com/view/franciscopernice/research",
"MIT thesis":"https://dspace.mit.edu/handle/1721.1/159909"}
def summary(n,b):
    s=b.decode("utf8","replace")
    if n=="arXiv subject query":
        x=ET.fromstring(b);return [" ".join(a.itertext()).strip() for a in x.iter() if a.tag.endswith("}title")]
    try:x=json.loads(s)
    except ValueError:
        txt=html.unescape(re.sub(r"<[^>]+>"," ",re.sub(r"<(script|style)\b.*?</\1>"," ",s,flags=re.I|re.S)))
        txt=re.sub(r"\s+"," ",txt)
        return {"prefix":txt[:340],"matches":[txt[max(0,m.start()-25):m.end()+58] for m in
            list(re.finditer(r"Potts|Weitz|2411\.06541|Access denied|verifying|sign in|no works match",txt,re.I))[:12]]}
    if n.startswith("Crossref"): return x["message"]["items"]
    if n=="OpenAlex original and references":return x
    if n.startswith("OpenAlex"):return [{"title":a.get("title"),"doi":a.get("doi")} for a in x.get("results",[])] if "results" in x else x
    if n=="Open Problems Catalog Q4813 followup":return {k:x.get(k) for k in ("title","state","merged","html_url","created_at")}
    if n.startswith("Semantic Scholar"):return x
    if n=="OpenReview":return [a.get("content",{}).get("title") for a in x.get("notes",[])] if "notes" in x else x
    if n.startswith("GitHub"):return {"total":x.get("total_count"),"hits":[[a.get("title",a.get("full_name")),a.get("html_url")] for a in x.get("items",[])]}
    if n=="DataCite query" and "data" in x:return {"total":x.get("meta",{}).get("total"),"hits":[[d["id"],d["attributes"]["titles"]] for d in x["data"]]}
    return str(x)[:2200]
def get(pair):
    n,url=pair
    cmd=["curl","-g","-LsS","--compressed","--connect-timeout","8","--max-time","24","-A","Potts classification bibliography 1.0"]
    if n=="Figshare":cmd+=["-H","Content-Type: application/json","--data",json.dumps({"search_for":Q,"limit":10})]
    p=subprocess.run([*cmd,"-w","\n%{http_code}",url],capture_output=True)
    b,_,code=p.stdout.rpartition(b"\n")
    row={"platform":n,"url":url,"utc":datetime.now(timezone.utc).isoformat(),"http":code.decode(),"exit":p.returncode,"bytes":len(b),"sha256":hashlib.sha256(b).hexdigest()}
    try:row["result"]=summary(n,b)
    except Exception as e:row["parse_error"]=repr(e)
    return row
if __name__=="__main__":
    with ThreadPoolExecutor(max_workers=8) as pool:rows=list(pool.map(get,urls.items()))
    orig=next(r for r in rows if r["platform"]=="OpenAlex original and references").get("result",{})
    ids=[i.split("/")[-1] for i in orig.get("referenced_works",[])] if isinstance(orig,dict) else []
    if ids:rows.append(get(("OpenAlex backward titles","https://api.openalex.org/works?select=id,title,doi&per_page=100&filter=openalex:"+"|".join(ids))))
    (Path(__file__).parent/"results"/"direct-search.json").write_text(json.dumps(rows,ensure_ascii=False,indent=2)+"\n",encoding="utf8")
    print(len(rows),"public requests recorded")
