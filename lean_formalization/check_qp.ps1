param([switch]$SkipBuild)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    $taskModules = @('QPGeometry', 'QPUniform', 'QPSlater', 'QPExistence', 'QPStrictNegative', 'FarkasMultipliers', 'QuadraticVariation', 'FiniteQPFirstOrder', 'FiniteQPKKT', 'QPLinearConstraints', 'QuadraticProgramKKT', 'FeasiblePositivity', 'KKTOrderPreparation', 'RowMomentNormalization', 'TransposeIdentities', 'KKTCoordinates', 'SlopeCurvature', 'KKTStrictOrder', 'KKTRowPositivity', 'PlateauRecurrences', 'FiniteIntervalSums', 'PlateauSums', 'NonterminalPlateau', 'TerminalPlateauSums', 'TerminalPlateau', 'OrderAndPlateaus', 'FlowBasics', 'FlowProbabilityPreparation', 'FlowProbabilities', 'ProductFlowSums', 'FlowConservation', 'FlowMoments', 'FlowMatrixAction', 'FlowSlopeAction', 'FlowSignRecurrence', 'FlowTransport', 'FlowEntrySums', 'FlowOffDiagonal', 'ProductFlow')
    $taskTheorems = @()
    foreach ($taskModule in $taskModules) {
        $taskText = Get-Content -LiteralPath ('PaperFramework/' + $taskModule + '.lean') -Raw
        # The kernel audit below also detects inline tactic admissions; an English
        # "admit" inside documentation is not a Lean proof shortcut.
        if ($taskText -match '\b(sorry|axiom|unsafe|native_decide)\b|(?m)^\s*admit\b') {
            throw "Forbidden proof shortcut in $taskModule."
        }
        foreach ($taskMatch in [regex]::Matches($taskText, '(?m)^theorem\s+(\w+)')) {
            $taskTheorems += 'CriticalExtrapolation.Paper.' + $taskMatch.Groups[1].Value
        }
    }
    if (-not $SkipBuild) {
        & lake build PaperFramework.QPStrictNegative PaperFramework.ProductFlow
        if ($LASTEXITCODE -ne 0) { throw 'Proved QP modules did not build.' }
    }
    $taskAudit = & lake env lean QPAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    $taskAuditText = $taskAudit -join "`n"
    if ($taskAuditText -match 'sorryAx') { throw 'QP proof depends on sorryAx.' }
    $taskAllowed = @('propext', 'Classical.choice', 'Quot.sound')
    $taskAxiomEntries = [regex]::Matches($taskAuditText, 'depends on axioms:\s*\[([^\]]*)\]')
    if ($taskAxiomEntries.Count -ne $taskTheorems.Count) { throw 'Audit entry count mismatch.' }
    foreach ($taskMatch in $taskAxiomEntries) {
        foreach ($taskAxiom in $taskMatch.Groups[1].Value -split ',') {
            if ($taskAxiom.Trim() -and $taskAxiom.Trim() -notin $taskAllowed) {
                throw "Unexpected axiom: $($taskAxiom.Trim())"
            }
        }
    }
    foreach ($taskTheorem in $taskTheorems) {
        if (-not $taskAuditText.Contains("'$taskTheorem'")) { throw "Missing audit: $taskTheorem" }
    }
    New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
    $taskAudit | Set-Content -LiteralPath 'verification/qp_axioms.txt' -Encoding utf8
    [ordered]@{
        scope = $taskModules -join ', '
        audited_theorems = $taskTheorems.Count
        sorryAx = $false
        complete_kkt_proved = $true
        feasible_positivity_proved = $true
        row_moment_normalization_proved = $true
        row_moment_positivity_proved = $true
        optimizer_strict_order_proved = $true
        plateau_endpoints_proved = $true
        flow_probabilities_proved = $true
        flow_conservation_proved = $true
        flow_row_moments_proved = $true
        flow_matrix_kernel_proved = $true
        flow_sign_recurrence_proved = $true
        output_multipliers_positive_proved = $true
        flow_matrix_signs_proved = $true
        flow_matrix_nonnegative_proved = $true
        paper_formalization_complete = $false
    } | ConvertTo-Json | Set-Content -LiteralPath 'verification/qp_summary.json' -Encoding utf8
    $taskFiles = @($taskModules | ForEach-Object { 'PaperFramework/' + $_ + '.lean' })
    $taskFiles += @('QPAudit.lean', 'check_qp.ps1')
    [ordered]@{
        date = '2026-10-12'
        scope = "$($taskTheorems.Count) audited QP, KKT, plateau and flow lemmas without sorryAx"
        foundation_manifest = 'source_manifest.json'
        energy_manifest = 'energy_source_manifest.json'
        files = @($taskFiles | ForEach-Object {
            [ordered]@{ path = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant() }
        })
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/qp_source_manifest.json' -Encoding utf8
    Write-Output "Verified $($taskTheorems.Count) QP lemmas including complete KKT without sorryAx. The paper proof remains incomplete."
} finally {
    Pop-Location
}







