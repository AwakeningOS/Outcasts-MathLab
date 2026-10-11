import gzip
import hashlib
import json
import sys
from pathlib import Path

run = Path(sys.argv[1])
root = run/'failure-atlas'
expected = {
 'failure_atlas_rows.json.gz':('d92e02ec37fd0577617f03fe3c390fd4f9343ecb1bca55d71865a4d4abf2044b',65987),
 'h2prime_rows.json.gz':('4c320c22ca8870b6671c36428767c886e037f538eb2b7dba2dfc650b9e1a06d7',71100),
 'exponent_rows.json.gz':('73b55b2260966d8df4359d88847493339cac01a25ca5a74dcfbb64177efb5b2d',None),
}
out=[]
for name,(sha,count) in expected.items():
    candidates=list(root.rglob(name))
    assert len(candidates)==1
    raw=gzip.decompress(candidates[0].read_bytes())
    digest=hashlib.sha256(raw).hexdigest()
    assert digest==sha
    rows=json.loads(raw)
    if isinstance(rows,dict):
        assert set(rows)=={'primes','squares'}
        row_groups={key:len(value) for key,value in rows.items()}
        rows=[item for value in rows.values() for item in value]
    else:
        row_groups=None
    assert isinstance(rows,list)
    assert count is None or len(rows)==count
    out.append({'file':name,'uncompressed_sha256':digest,'rows':len(rows),'row_groups':row_groups,'all_rows_valid_json':True})
record={'verified':out,'author_scripts_executed':False,'monte_carlo_reproduced':False,'independence_or_higher_order_test_performed':False}
(run/'atlas-row-verification.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
