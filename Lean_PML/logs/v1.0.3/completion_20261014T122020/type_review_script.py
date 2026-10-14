from pathlib import Path
import subprocess,json
root=Path.cwd();folder=root/(root/'logs/v1.0.3/current_completion_path.txt').read_text().strip()
names=['LeanPML.PML.RegionalWeakCoefficient','LeanPML.PML.SeparatedRegionalWeakCoefficients','LeanPML.PML.WeakRegionalAbsorption','LeanPML.PML.Weak.OriginalAt','LeanPML.PML.Weak.OriginalInterval','LeanPML.PML.Weak.OriginalJet','LeanPML.PML.Weak.DegenerateJetCompatibility','LeanPML.PML.Weak.CompatibleLift','LeanPML.PML.Weak.OriginalInterval.EnergyConclusions','LeanPML.PML.Weak.main_energy_estimate_RegionalWeak','LeanPML.PML.Weak.OriginalInterval.main_energy_estimate_WeakOriginal','LeanPML.Examples.WeakStaticMode.nonzero_static_regression','LeanPML.Examples.WeakBranchRegression.all_four_configurations']
p=folder/'TypeReview.lean';p.write_text('import LeanPML\nset_option pp.universes false\n'+''.join('#print '+n+'\n' for n in names))
subprocess.run(['python3','scripts/run_logged.py','--stage','v1.0.3','final_type_review','lake','env','lean',str(p.relative_to(root))],check=True)
