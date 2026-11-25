"""Public-source search ledger. Only metadata, paths and excerpts are retained."""
import concurrent.futures
import datetime as dt
import json
import re
import urllib.error
import urllib.parse
import urllib.request

def url(base, **params):
    return base + "?" + urllib.parse.urlencode(params)

def read(endpoint):
    request = urllib.request.Request(endpoint, headers={"User-Agent": "ShellsortResearchReview/1.0"})
    with urllib.request.urlopen(request, timeout=24) as response:
        return response.read(6_000_000).decode("utf-8", "replace")

def summarize(name, endpoint):
    try:
        raw = read(endpoint)
        if name == "OpenAlex":
            j = json.loads(raw)
            results = [(x["display_name"], x.get("doi")) for x in j["results"]]
        elif name == "Crossref":
            results = [(x.get("title"), x.get("DOI")) for x in json.loads(raw)["message"]["items"]]
        elif name == "DBLP":
            hits = json.loads(raw)["result"]["hits"]
            results = [(x["info"]["title"], x["info"]["url"]) for x in hits.get("hit", [])]
        elif name == "Semantic Scholar":
            results = [(x["title"], x["url"]) for x in json.loads(raw)["data"]]
        elif name == "GitHub repositories":
            results = [(x["full_name"], x["html_url"]) for x in json.loads(raw)["items"]]
        elif name.startswith("tree "):
            j = json.loads(raw)
            paths = [x["path"] for x in j["tree"] if x["type"] == "blob"]
            terms = re.compile(r"shell|worst|minimax|optimum|increment|average|README", re.I)
            matches = [p for p in paths if terms.search(p)]
            results = dict(sha=j.get("sha"), truncated=j["truncated"], files=len(paths),
                           matching_files=len(matches), sample=matches[:12],
                           worst_case_paths=[p for p in paths if re.search(r"minimax|worst", p, re.I)][:30])
        elif name == "OEIS":
            j = json.loads(raw)
            results = [(x["number"], x["name"]) for x in (j or [])][:10]
        elif name == "arXiv":
            results = [re.sub(r"\s+", " ", s).strip() for s in re.findall(r"<title>(.*?)</title>",raw,re.S)][:10]
        else:
            from html import unescape
            title = re.search(r"<title[^>]*>(.*?)</title>", raw, re.I|re.S)
            results = dict(page_title=unescape(re.sub(r"\s+", " ", title[1])).strip() if title else None,
                           challenge=bool(re.search(r"captcha|verify you are human|just a moment|unusual traffic", raw, re.I)),
                           snippet=re.sub(r"\s+", " ", re.sub(r"<[^>]*>", " ", raw))[:170])
        return dict(source=name, url=endpoint, result=results)
    except Exception as e:
        return dict(source=name, url=endpoint, error=str(e))

def main():
    q = "Shellsort worst case optimal gap sequences"
    urls = []
    for phrase in (q, "Shellsort subset dynamic programming", "Shellsort two pass worst case comparisons"):
        urls += [
            ("OpenAlex", url("https://api.openalex.org/works",search=phrase,per_page=6)),
            ("Crossref", url("https://api.crossref.org/works", **{"query.bibliographic":phrase,"rows":5})),
            ("Semantic Scholar", url("https://api.semanticscholar.org/graph/v1/paper/search",query=phrase,limit=5,fields="title,url")),
        ]
    urls += [
        ("arXiv", url("https://export.arxiv.org/api/query",search_query='all:shellsort AND (all:optimal OR all:worst)', max_results=12)),
        ("DBLP", url("https://dblp.org/search/publ/api",q="Shellsort",format="json",h=20)),
        ("Google Scholar",url("https://scholar.google.com/scholar",q=q)),
        ("ACM",url("https://dl.acm.org/action/doSearch",AllField=q)),
        ("IEEE",url("https://ieeexplore.ieee.org/search/searchresult.jsp",queryText=q)),
        ("Springer",url("https://link.springer.com/search",query=q)),
        ("MathSciNet",url("https://mathscinet.ams.org/mathscinet/publications-search",query="Shellsort")),
        ("zbMATH",url("https://zbmath.org/",q="Shellsort")),
        ("OEIS",url("https://oeis.org/search",q="14,18,23,29,35,41,48,56,64,71,78",fmt="json")),
        ("GitHub repositories",url("https://api.github.com/search/repositories",q="shellsort optimal",per_page=20)),
        ("GitHub repositories",url("https://api.github.com/search/repositories",q="shellsort minimax",per_page=20)),
    ]
    repos = ["mkdokken/ShellSort","EternalYMZ/Project-S","LeanPool/lean-pool",
             "Nannde/shellsort-three-pass-optimality","openai/math"]
    urls.extend(("tree "+r, "https://api.github.com/repos/"+r+"/git/trees/HEAD?recursive=1") for r in repos)
    print(json.dumps({"UTC":dt.datetime.now(dt.timezone.utc).isoformat(),"queries":len(urls)}),flush=True)
    with concurrent.futures.ThreadPoolExecutor(6) as workers:
        for result in workers.map(lambda item:summarize(*item),urls):
            print(json.dumps(result, ensure_ascii=True),flush=True)

if __name__ == "__main__":
    main()
