#!/usr/bin/env python3
"""Verify the rectangular MS analytic sampler; no numerical/runtime claim."""
from pathlib import Path
import argparse, hashlib, json, re, subprocess
from check_proof import source_admissions

ROOT = Path(__file__).resolve().parent
MODULE = 'MatrixSpencer.DyadicManuscriptAnalyticAlgorithm'
AUDIT = ROOT / '.verification/ms_rectangular_analytic'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def closure():
    seen = set()
    def visit(m):
        if not m.startswith('MatrixSpencer.') or m in seen:
            return
        p = ROOT / (m.replace('.', '/') + '.lean')
        seen.add(m)
        for line in p.read_text().splitlines():
            if line.startswith('import '):
                for name in line[7:].split('--', 1)[0].split():
                    visit(name)
    visit(MODULE)
    return sorted(seen)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--timeout', type=int, default=7200)
    args = ap.parse_args()
    if args.timeout <= 0:
        ap.error('timeout must be positive')
    AUDIT.mkdir(parents=True, exist_ok=True)
    result = {'status':'INCOMPLETE', 'root':MODULE,
              'polynomial_runtime_verified':False, 'real_ram_execution_verified':False,
              'numerical_implementation_verified':False,
              'extracted_executable':False, 'commands':[]}
    def run(label, argv):
        with (AUDIT / (label+'.log')).open('w') as out:
            p = subprocess.run(argv, cwd=ROOT, stdout=out, stderr=subprocess.STDOUT, timeout=args.timeout)
        result['commands'].append({'label':label, 'argv':argv, 'exit_code':p.returncode})
        if p.returncode:
            raise ValueError(label+' failed')
        return (AUDIT / (label+'.log')).read_text()
    try:
        modules = closure()
        files = [m.replace('.', '/')+'.lean' for m in modules]
        files += ['check_ms_rectangular_analytic.py','check_proof.py','tools/Replay.lean',
                  'tools/MSRectangularAnalyticPrimitive.lean','tools/MSRectangularAnalyticRoutes.lean',
                  'lean-toolchain','lakefile.toml','lake-manifest.json','run_lake.sh',
                  'MS_RECTANGULAR_ANALYTIC_SAMPLER_PROOF.md']
        before = {p:digest(ROOT/p) for p in files}
        admissions = {p:source_admissions((ROOT/p).read_text()) for p in files if p.endswith('.lean')}
        if any(admissions.values()):
            raise ValueError('Admission tokens in checked sources: '+str({p:a for p,a in admissions.items() if a}))
        wrapper = str(ROOT/'run_lake.sh')
        run('build',[wrapper,'build',MODULE])
        probe = run('primitive',[wrapper,'env','lean','tools/MSRectangularAnalyticPrimitive.lean'])
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",probe)
        expected = {'MSRectangularAnalyticPrimitive.rectangular_return','MSRectangularAnalyticPrimitive.rectangular_success',
                    'MSRectangularAnalyticPrimitive.rectangular_weights'}
        if len(reports)!=3 or {n for n,_ in reports}!=expected:
            raise ValueError('Missing independent primitive endpoint checks')
        if any(set(n.strip() for n in ax.split(','))-ALLOWED for _,ax in reports):
            raise ValueError('Unexpected primitive axiom dependencies')
        routes = run('routes',[wrapper,'env','lean','tools/MSRectangularAnalyticRoutes.lean'])
        if 'MS_RECTANGULAR_ANALYTIC_ROUTE_CHECKED ' not in routes:
            raise ValueError('Declared analytic/proof route audit did not finish')
        replay = run('replay',[wrapper,'env','lean','--run','tools/Replay.lean',MODULE])
        checked = sorted(re.findall(r'^REPLAYED ([^:]+):',replay,re.M))
        audited = sorted(re.findall(r'^PROJECT_AXIOMS_CHECKED ([^:]+):',replay,re.M))
        if checked != modules or audited != modules or 'PANIC' in replay:
            raise ValueError('Kernel replay/axiom audit missed actual project dependencies')
        if any(digest(ROOT/p)!=h for p,h in before.items()):
            raise ValueError('Verification inputs changed during checking')
        result.update(status='VERIFIED',source_sha256=before,local_import_closure_modules=len(modules),
                      same_kernel_replay_in_separate_process=True,independent_kernel_implementation=False,
                      fresh_mathlib_replay=False,all_local_declarations_standard_axioms_only=True,
                      scope='Rectangular MS finite analytic sampler: actual original full-sign outputs have norm at most6796548sqrt(Nlog(2D/N)), normalized finite weights and actual success probability at least1/2 at the explicit retry count. Analytic preparation, support mesh, spectral sampler and exact three-term score remain; no numerical algorithm or runtime certificate.')
    except (OSError,ValueError,subprocess.TimeoutExpired) as e:
        result['reason'] = str(e)
    (AUDIT/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status']+': '+result.get('reason',result.get('scope','')))
    return 0 if result['status']=='VERIFIED' else 2

if __name__ == '__main__':
    raise SystemExit(main())
