param([switch]$SkipBuild)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    $taskModules = @('TailTransform', 'TridiagonalStructure', 'MatrixPositivity', 'CorrectionMatrix', 'ObjectiveEnergy', 'TailEnergyIdentities', 'TridiagonalQuadratic', 'EnergyIdentity', 'ChainMatrix', 'Energy', 'RelativeConvexity', 'QPValue')
    $taskTheorems = @()
    foreach ($taskModule in $taskModules) {
        $taskText = Get-Content -LiteralPath ('PaperFramework/' + $taskModule + '.lean') -Raw
        if ($taskText -match '\b(sorry|admit|axiom|unsafe|native_decide)\b') {
            throw "Forbidden proof shortcut in $taskModule."
        }
        foreach ($taskMatch in [regex]::Matches($taskText, '(?m)^theorem\s+(\w+)')) {
            $taskTheorems += 'CriticalExtrapolation.Paper.' + $taskMatch.Groups[1].Value
        }
    }
    if (-not $SkipBuild) {
        & lake build PaperFramework.RelativeConvexity PaperFramework.QPValue
        if ($LASTEXITCODE -ne 0) { throw 'Proved energy modules did not build.' }
    }
    $taskAudit = & lake env lean EnergyAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    $taskAuditText = $taskAudit -join "`n"
    if ($taskAuditText -match 'sorryAx') { throw 'Energy proof depends on sorryAx.' }
    $taskAllowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($taskMatch in [regex]::Matches($taskAuditText, 'depends on axioms:\s*\[([^\]]*)\]')) {
        foreach ($taskAxiom in $taskMatch.Groups[1].Value -split ',') {
            if ($taskAxiom.Trim() -and $taskAxiom.Trim() -notin $taskAllowed) {
                throw "Unexpected axiom: $($taskAxiom.Trim())"
            }
        }
    }
    foreach ($taskTheorem in $taskTheorems) {
        if (-not $taskAuditText.Contains("'$taskTheorem'")) { throw "Missing audit: $taskTheorem" }
    }
    $taskAudit | Set-Content -LiteralPath 'verification/energy_axioms.txt' -Encoding utf8
    [ordered]@{
        scope = $taskModules -join ', '
        audited_theorems = $taskTheorems.Count
        sorryAx = $false
        paper_formalization_complete = $false
    } | ConvertTo-Json | Set-Content -LiteralPath 'verification/energy_summary.json' -Encoding utf8
    Write-Output "Verified $($taskTheorems.Count) energy lemmas without sorryAx. The paper proof remains incomplete."
} finally {
    Pop-Location
}
