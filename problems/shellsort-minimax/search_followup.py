"""Fallback public endpoints and citation chaining for the source audit."""
import json
import sys
from pathlib import Path
from urllib.parse import urlencode
sys.path.insert(0,str(Path(__file__).resolve().parent))
from search_sources import read
from concurrent.futures import ThreadPoolExecutor

def inspect(item):
    name,url=item
    try:
        j=json.loads(read(url))
        if name=="OpenAlex citations":
            result=[(x.get("publication_date"),x.get("display_name"),x.get("doi")) for x in j["results"]]
        elif name=="zbMATH":
            result=[{"title":x.get("title"),"id":x.get("identifier"),"year":x.get("year"),
                     "authors":[a.get("name") for a in x.get("contributors",{}).get("authors",[])]}
                    for x in j.get("result",[])]
        elif name.startswith("DBLP"):
            result=j.get("result",j.get("title",j))
            if isinstance(result,dict):result=str(result)[:700]
        else:
            result={k:j.get(k) for k in ("title","year","citationCount","url","citations")}
        return dict(service=name,url=url,result=result)
    except Exception as e:return dict(service=name,url=url,error=str(e))

def main():
    queries=[("DBLP author record","https://dblp.org/rec/journals/corr/abs-2112-11127.json"),
             ("DBLP mirror","https://dblp.uni-trier.de/search/publ/api?q=shellsort&h=10&format=json"),
             ("Semantic Scholar record","https://api.semanticscholar.org/graph/v1/paper/ARXIV:2112.11127?fields=title,year,citationCount,citations.title,url"),
             ("zbMATH","https://api.zbmath.org/v1/document/_search?"+urlencode({"search_string":"ti:shellsort","results_per_page":100}))]
    try:
        j=json.loads(read("https://api.openalex.org/works/https://doi.org/10.48550/arxiv.2112.11127"))
        ident=j["id"].split("/")[-1]
        queries.append(("OpenAlex citations","https://api.openalex.org/works?"+urlencode({"filter":"cites:"+ident+",to_publication_date:2026-11-25","per_page":100})))
    except Exception as e:print(json.dumps({"service":"OpenAlex Lee lookup","error":str(e)}))
    with ThreadPoolExecutor(5) as ex:
        for info in ex.map(inspect,queries):print(json.dumps(info,ensure_ascii=True),flush=True)
if __name__=="__main__":main()
