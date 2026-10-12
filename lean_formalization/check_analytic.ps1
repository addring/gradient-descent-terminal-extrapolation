param([switch]$SkipBuild)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    $taskModules = @('InstanceBounds', 'VectorQuadratic', 'ForwardNonnegativity', 'ForwardFlowAlgebra', 'InitialInterval', 'FeasibleFloor', 'NormalizedEnergyBound', 'ShiftedEnergy', 'EnergyLowerBound', 'TrialBasics', 'TrialSlopeScalar', 'TrialRightScalar', 'TrialFunctional', 'TrialProfiles', 'TrialDirection', 'TrialNormalization', 'ScaledParameters', 'UniformSigns', 'NegativeAlgebra', 'VecTwo', 'NegativeRadius', 'NegativeSmall', 'NegativePolynomial', 'ReferenceRatio', 'FiniteLowerAtOne', 'TrialBaseline', 'TrialMajorant', 'NegativeLocalSlacks', 'NegativeLeading', 'NegativeBackward', 'NegativeSlackSigns', 'NegativeAllSlacks', 'NegativeData', 'ConjugateBasics', 'ConjugatePotential', 'ConjugateGrowth', 'ConjugateExistence', 'RecoveredSmoothness', 'RecoveredInterpolation', 'FunctionDilation', 'PerturbationTrajectory', 'InstanceDilation', 'PerturbationRecovery', 'NegativeInstance', 'FirstOrderConvex', 'SmoothDescent', 'PositiveQuadraticContinuity', 'ChainContinuity', 'QuadraticActual', 'LargeQuadratic', 'SmoothnessNormalization', 'WorstScaling', 'FlatEnvelopeData', 'FlatEnvelopeAttainment', 'FlowQuadratic', 'FlowVectorQuadratic', 'FlowTrajectory', 'FlowSlackAlgebra', 'FlowIdentityProof', 'FullConjugatePotential', 'FullConjugateGrowth', 'FullConjugateExistence', 'FullRecoveredSmoothness', 'FullRecoveredInterpolation', 'RadiusCoordinates', 'RadiusInstance', 'TrialUniformAlgebra', 'TrialUniformLimitProof', 'TrialPerturbationAlgebra', 'TrialPerturbationProfiles', 'TrialWeightedAlgebra', 'TrialHarmonicBounds', 'TrialWeightedPointwise', 'TrialWeightedSum', 'TrialPerturbationProof', 'TrialReferenceAlgebra', 'TrialFiniteAbel', 'TrialReferenceModel', 'TrialReferenceTail', 'TrialReferenceErrorPointwise', 'TrialReferenceTailSum', 'TrialReferenceEnergyPointwise', 'TrialReferenceFiniteBounds', 'TrialReferenceEnergyError', 'TrialReferencePoleLimit', 'TrialReferenceSumLimit', 'TrialReferenceModelLimit', 'UniformScaledAlgebra', 'UniformMassBounds', 'UniformErrorBounds', 'TrialAsymptotics', 'UniformTerminalBounds', 'UniformLowerLimit', 'TrialScaledIdentity', 'TrialScaledLimitProof', 'UniformAuxiliaryProof', 'UniformLimit')
    $taskTheorems = @()
    foreach ($taskModule in $taskModules) {
        $taskText = Get-Content -LiteralPath ('PaperFramework/' + $taskModule + '.lean') -Raw -Encoding utf8
        if ($taskText -match '\b(sorry|axiom|unsafe|native_decide)\b|(?m)^\s*admit\b') {
            throw "Forbidden proof shortcut in $taskModule."
        }
        foreach ($taskMatch in [regex]::Matches($taskText, '(?m)^theorem\s+(\w+)')) {
            $taskTheorems += 'CriticalExtrapolation.Paper.' + $taskMatch.Groups[1].Value
        }
    }
    if (-not $SkipBuild) {
        & lake build PaperFramework.InstanceBounds PaperFramework.ForwardNonnegativity PaperFramework.ForwardFlowAlgebra PaperFramework.InitialInterval PaperFramework.EnergyLowerBound PaperFramework.TrialNormalization PaperFramework.UniformSigns PaperFramework.NegativeSmall PaperFramework.NegativePolynomial PaperFramework.ReferenceRatio PaperFramework.FiniteLowerAtOne PaperFramework.TrialMajorant PaperFramework.NegativeLocalSlacks PaperFramework.NegativeData PaperFramework.ConjugateBasics PaperFramework.NegativeInstance PaperFramework.SmoothDescent PaperFramework.ChainContinuity PaperFramework.LargeQuadratic PaperFramework.WorstScaling PaperFramework.FlatEnvelopeAttainment PaperFramework.FlowIdentityProof PaperFramework.FullRecoveredInterpolation PaperFramework.RadiusInstance PaperFramework.TrialUniformLimitProof PaperFramework.TrialPerturbationProfiles PaperFramework.TrialPerturbationProof PaperFramework.TrialReferenceModel PaperFramework.TrialFiniteAbel PaperFramework.TrialReferenceTail PaperFramework.TrialReferenceErrorPointwise PaperFramework.TrialReferenceTailSum PaperFramework.TrialReferenceEnergyPointwise PaperFramework.TrialReferenceFiniteBounds PaperFramework.TrialReferenceEnergyError PaperFramework.TrialReferencePoleLimit PaperFramework.TrialReferenceSumLimit PaperFramework.TrialReferenceModelLimit PaperFramework.UniformScaledAlgebra PaperFramework.UniformMassBounds PaperFramework.UniformErrorBounds PaperFramework.TrialAsymptotics PaperFramework.UniformTerminalBounds PaperFramework.UniformLowerLimit PaperFramework.TrialScaledIdentity PaperFramework.TrialScaledLimitProof PaperFramework.UniformAuxiliaryProof PaperFramework.UniformLimit
        if ($LASTEXITCODE -ne 0) { throw 'Proved analytic modules did not build.' }
    }
    $taskAudit = & lake env lean AnalyticAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    $taskAuditText = $taskAudit -join "`n"
    if ($taskAuditText -match 'sorryAx') { throw 'Analytic proof depends on sorryAx.' }
    $taskAllowed = @('propext', 'Classical.choice', 'Quot.sound')
    $taskEntries = [regex]::Matches($taskAuditText, 'depends on axioms:\s*\[([^\]]*)\]')
    if ($taskEntries.Count -ne $taskTheorems.Count) { throw 'Audit entry count mismatch.' }
    foreach ($taskEntry in $taskEntries) {
        foreach ($taskAxiom in $taskEntry.Groups[1].Value -split ',') {
            if ($taskAxiom.Trim() -and $taskAxiom.Trim() -notin $taskAllowed) {
                throw "Unexpected axiom: $($taskAxiom.Trim())"
            }
        }
    }
    foreach ($taskTheorem in $taskTheorems) {
        if (-not $taskAuditText.Contains("'$taskTheorem'")) { throw "Missing audit: $taskTheorem" }
    }
    $taskCompleteRecord = Get-Content -LiteralPath 'verification/complete_summary.json' -Raw | ConvertFrom-Json
    $taskCompleteManifest = Get-Content -LiteralPath 'verification/complete_source_manifest.json' -Raw | ConvertFrom-Json
    $taskCompleteCurrent = ($taskCompleteRecord.separate_full_build -and -not $taskCompleteRecord.sorryAx -and
        $taskCompleteRecord.direct_sorry_count -eq 0)
    foreach ($taskCompleteFile in $taskCompleteManifest.files) {
        if ((Get-FileHash -LiteralPath $taskCompleteFile.path -Algorithm SHA256).Hash.ToLowerInvariant() -ne $taskCompleteFile.sha256) {
            $taskCompleteCurrent = $false
        }
    }
    $taskAudit | Set-Content -LiteralPath 'verification/analytic_axioms.txt' -Encoding utf8
    [ordered]@{
        scope = $taskModules -join ', '
        audited_theorems = $taskTheorems.Count
        sorryAx = $false
        actual_supremum_nonempty_bounded_proved = $true
        vector_quadratic_nonnegative_proved = $true
        forward_remainder_nonnegative_proved = $true
        forward_potentials_cancel_proved = $true
        scaled_limit_of_interval_sandwich_proved = $true
        all_feasible_energy_lower_bound_proved = $true
        trial_normalization_and_differences_proved = $true
        trial_strict_feasibility_proved = $true
        trial_normalization_asymptotic_proved = $true
        scaled_parameter_coordinates_proved = $true
        finite_counterexample_radius_expansion_proved = $true
        ordinary_slack_polynomial_proved = $true
        ordinary_slack_parameters_corrected = $true
        finite_unit_step_lower_interval_proved = $true
        trial_reference_remainder_majorant_proved = $true
        counterexample_adjacent_and_distinguished_slacks_proved = $true
        all_directed_counterexample_slacks_proved = $true
        strict_negative_finite_data_proved = $true
        conjugate_optimizer_value_proved = $true
        conjugate_global_existence_uniqueness_proved = $true
        conjugate_global_smoothness_proved = $true
        special_finite_interpolation_proved = $true
        actual_perturbation_trajectory_proved = $true
        actual_instance_dilation_proved = $true
        global_counterexample_function_proved = $true
        smooth_convex_interpolation_necessity_proved = $true
        positive_chain_neighborhood_proved = $true
        chain_flow_admissibility_proved = $true
        actual_quadratic_large_coefficient_failure_proved = $true
        actual_worst_gradient_scaling_proved = $true
        actual_envelope_attainment_proved = $true
        envelope_attainment_method = 'global recovery of the Huber finite trajectory; the extension may differ from piecewise Huber'
        forward_flow_identity_proved = $true
        general_finite_interpolation_proved = $true
        radius_equality_embedding_proved = $true
        trial_uniform_normalization_composition_proved = $true
        genuine_trial_parameter_perturbation_proved = $true
        genuine_trial_energy_estimates_proved = $true
        paper_formalization_complete = $taskCompleteCurrent
    } | ConvertTo-Json | Set-Content -LiteralPath 'verification/analytic_summary.json' -Encoding utf8
    $taskFiles = @($taskModules | ForEach-Object { 'PaperFramework/' + $_ + '.lean' })
    $taskFiles += @('AnalyticAudit.lean', 'check_analytic.ps1')
    [ordered]@{
        date = '2026-10-12'
        scope = "$($taskTheorems.Count) audited analytic and forward algebra lemmas without sorryAx"
        foundation_manifest = 'source_manifest.json'
        qp_manifest = 'qp_source_manifest.json'
        files = @($taskFiles | ForEach-Object {
            [ordered]@{ path = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant() }
        })
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/analytic_source_manifest.json' -Encoding utf8
    Write-Output "Verified $($taskTheorems.Count) analytic and forward algebra lemmas without sorryAx. Current separate full-proof checkpoint=$taskCompleteCurrent."
} finally {
    Pop-Location
}
