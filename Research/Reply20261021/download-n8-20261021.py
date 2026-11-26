import pathlib, urllib.request, json

root = pathlib.Path(__file__).resolve().parent
pin = '3d17d5e83cd68b9bea71371155a56d6097644a9b'
files = ('README.md','SHA256SUMS','contract.md','n8_primes.jsonl.gz','n8_results.json','n8_rows.csv.gz','n8scan.py','run.log','selftest.log','selftest_results.json')
dest = root / 'source'
dest.mkdir(exist_ok=True)
for name in files:
    url = f'https://raw.githubusercontent.com/betyourluck/Outcasts-MathLab/{pin}/Research/Holdout1e8Scan20261020/{name}'
    with urllib.request.urlopen(url, timeout=30) as response, (dest/name).open('wb') as out:
        while chunk := response.read(1048576):
            out.write(chunk)
    print(json.dumps({'file':name,'bytes':(dest/name).stat().st_size}),flush=True)
