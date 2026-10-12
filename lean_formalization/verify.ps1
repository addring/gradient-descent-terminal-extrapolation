param([switch]$FetchCache)
$ErrorActionPreference = 'Stop'
$taskProject = $PSScriptRoot
Push-Location -LiteralPath $taskProject
try {
    $taskLeanVersion = & lean --version 2>&1
    if ($LASTEXITCODE -ne 0 -or ($taskLeanVersion -join "`n") -notmatch 'version 4\.26\.0[,)]') {
        throw "Incorrect Lean version: $($taskLeanVersion -join ' ')"
    }
    $taskSources = @(Get-ChildItem -LiteralPath 'CriticalExtrapolation' -Filter '*.lean' -Recurse)
    $taskSources += Get-Item -LiteralPath 'CriticalExtrapolation.lean'
    $taskBad = $taskSources | Select-String -Pattern '\b(sorry|admit|axiom|unsafe|native_decide)\b'
    if ($taskBad) {
        $taskBad | ForEach-Object { Write-Output $_ }
        throw 'Forbidden proof shortcut in project sources.'
    }
    if ($FetchCache) {
        & lake exe cache get
        if ($LASTEXITCODE -ne 0) { throw 'mathlib cache download failed.' }
    }
    & lake build CriticalExtrapolation
    if ($LASTEXITCODE -ne 0) { throw 'Lean project build failed.' }
    $taskManifest = Get-Content -LiteralPath 'lake-manifest.json' -Raw | ConvertFrom-Json
    foreach ($taskPackage in $taskManifest.packages) {
        if ($taskPackage.type -eq 'git') {
            $taskPackagePath = Join-Path '.lake\packages' $taskPackage.name
            $taskActualRev = & git -C $taskPackagePath rev-parse HEAD
            if ($LASTEXITCODE -ne 0 -or $taskActualRev.Trim() -ne $taskPackage.rev) {
                throw "Dependency revision mismatch: $($taskPackage.name)"
            }
            & git -C $taskPackagePath diff --quiet
            if ($LASTEXITCODE -ne 0) { throw "Modified dependency source: $($taskPackage.name)" }
        }
    }
    $taskAudit = & lake env lean AxiomAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    $taskAudit | ForEach-Object { Write-Output $_ }
    if (($taskAudit -join "`n") -match 'sorryAx') { throw 'A theorem depends on sorryAx.' }
    $taskAllowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')
    $taskAxiomMatches = [regex]::Matches(($taskAudit -join "`n"), 'depends on axioms:\s*\[([^\]]*)\]')
    foreach ($taskMatch in $taskAxiomMatches) {
        foreach ($taskAxiom in ($taskMatch.Groups[1].Value -split ',')) {
            if ($taskAxiom.Trim() -notin $taskAllowedAxioms) {
                throw "Unexpected theorem axiom: $($taskAxiom.Trim())"
            }
        }
    }
    New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
    $taskAudit | Set-Content -LiteralPath 'verification\axioms.txt' -Encoding utf8
    Write-Output 'Current modules checked. This does not certify the unfinished paper.'
} finally {
    Pop-Location
}
