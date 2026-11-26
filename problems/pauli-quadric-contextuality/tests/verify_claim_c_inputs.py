"""Check the original signed-census inputs against their archived digests."""
from csv import DictReader
from hashlib import sha256
from io import StringIO
from pathlib import Path
from zipfile import ZipFile

ROOT=Path(__file__).resolve().parents[1]
def check():
    archive_hashes = {}
    for line in (ROOT/'sources'/'SHA256SUMS').read_text(encoding='ascii').splitlines():
        expected, name = line.split()
        archive_hashes[name] = expected
    paths=['L7R_CERTS_42.txt','frames.txt','level1_list.txt','level1_words.tsv',
           'closure_words.tsv','point_words.tsv','sigma42.txt']
    paths += [f'level2_{kind}_{i:02d}.txt' for i in range(18) for kind in ('inst','comp')]
    print('sha256\tbytes\tinput')
    for name in ('jonah-proof.zip','jonah-evidence.zip'):
        data=(ROOT/'sources'/name).read_bytes();digest=sha256(data).hexdigest()
        if archive_hashes[name]!=digest:
            raise ValueError('source retrieval mismatch: '+name)
        print(digest,len(data),name,sep='\t')
    with ZipFile(ROOT/'sources/jonah-proof.zip') as z:
        text=z.read('MANIFEST_CPL_ALL.tsv').decode().splitlines()
        manifest={r['path']:r for r in DictReader(StringIO('\n'.join(text[1:])),delimiter='\t')}
        for short in paths:
            path='data/'+short; row=manifest[path]; data=z.read('CPL/'+path);digest=sha256(data).hexdigest()
            if row['in_zip']!='yes' or int(row['bytes'])!=len(data) or row['sha256']!=digest:
                raise ValueError('archived entry mismatch: '+path)
            print(digest,len(data),'CPL/'+path,sep='\t')
        cert=z.read('CPL/data/L7R_CERTS_42.txt')
    with ZipFile(ROOT/'sources/jonah-evidence.zip') as z:
        [name]=[n for n in z.namelist() if n.endswith('/cert/L7R_CERTS_42.txt')]
        if z.read(name)!=cert:raise ValueError('certificate copies differ')
    return 0

if __name__=='__main__':raise SystemExit(check())
