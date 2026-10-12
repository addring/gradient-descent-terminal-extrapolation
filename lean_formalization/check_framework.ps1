param([switch]$SkipBuild)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    if (-not $SkipBuild) {
        & lake build PaperFramework
        if ($LASTEXITCODE -ne 0) { throw 'Framework build failed.' }
    }
    $taskAudit = & lake env lean FrameworkAudit.lean 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    New-Item -ItemType Directory -Path 'verification' -Force | Out-Null
    $taskAudit | Set-Content -LiteralPath 'verification\framework_axioms.txt' -Encoding utf8
    $taskAudit | ForEach-Object { Write-Output $_ }
    $taskInventory = @()
    $taskImports = @()
    foreach ($taskFile in (Get-ChildItem -LiteralPath 'PaperFramework' -Filter '*.lean' | Sort-Object Name)) {
        $taskText = Get-Content -LiteralPath $taskFile.FullName -Raw
        if ($taskText -match '(?m)^\s*(axiom|unsafe)\b|\bnative_decide\b') {
            throw "Unexpected shortcut: $($taskFile.Name)"
        }
        $taskMatches = [regex]::Matches($taskText, '(?m)^theorem\s+(\w+)')
        for ($taskIndex = 0; $taskIndex -lt $taskMatches.Count; $taskIndex++) {
            $taskStart = $taskMatches[$taskIndex].Index
            $taskEnd = $taskText.Length
            if ($taskIndex + 1 -lt $taskMatches.Count) { $taskEnd = $taskMatches[$taskIndex + 1].Index }
            $taskBlock = $taskText.Substring($taskStart, $taskEnd - $taskStart)
            $taskHoles = [regex]::Matches($taskBlock, '(?m)^\s*sorry\b').Count
            $taskInventory += [ordered]@{
                theorem = 'CriticalExtrapolation.Paper.' + $taskMatches[$taskIndex].Groups[1].Value
                file = 'PaperFramework/' + $taskFile.Name
                line = 1 + [regex]::Matches($taskText.Substring(0, $taskStart), "`n").Count
                direct_sorry_count = $taskHoles
                status = $(if ($taskHoles -gt 0) { 'admitted' } else { 'composition; dependencies require audit' })
            }
        }
        $taskImports += [ordered]@{
            module = 'PaperFramework.' + $taskFile.BaseName
            imports = @([regex]::Matches($taskText, '(?m)^import\s+(\S+)') |
                ForEach-Object { $_.Groups[1].Value })
        }
    }
    $taskInventory | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification\framework_obligations.json' -Encoding utf8
    $taskImports | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification\framework_imports.json' -Encoding utf8
    $taskHoleCount = 0
    foreach ($taskObligation in $taskInventory) {
        $taskHoleCount += $taskObligation['direct_sorry_count']
    }
    $taskContainsSorryAx = (($taskAudit -join "`n") -match 'sorryAx')
    $taskProofComplete = ($taskHoleCount -eq 0 -and -not $taskContainsSorryAx)
    [ordered]@{
        stage = $(if ($taskProofComplete) {
            'main entry fully proved; inventory includes auxiliary modules; see complete audit for every theorem'
        } else { 'main entry compiles; proof incomplete; inventory includes auxiliary modules' })
        theorem_count = $taskInventory.Count
        direct_sorry_count = $taskHoleCount
        framework_audit_contains_sorryAx = $taskContainsSorryAx
        lean = '4.26.0'
        mathlib = '2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
    } | ConvertTo-Json | Set-Content -LiteralPath 'verification\framework_summary.json' -Encoding utf8
    $taskFiles = @(Get-ChildItem -LiteralPath 'PaperFramework' -Filter '*.lean' | Sort-Object Name |
        ForEach-Object { 'PaperFramework/' + $_.Name })
    $taskFiles += @('PaperFramework.lean', 'FrameworkAudit.lean', 'check_framework.ps1',
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
    [ordered]@{
        date = '2026-10-12'
        scope = $(if ($taskProofComplete) {
            'paper framework with proved main entry; see complete audit for every theorem'
        } else { 'paper framework; full proof incomplete; see independent audits for proved subchains' })
        files = @($taskFiles | ForEach-Object {
            [ordered]@{ path = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant() }
        })
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath 'verification/framework_source_manifest.json' -Encoding utf8
    Write-Output "Framework: $($taskInventory.Count) theorems, $taskHoleCount direct proof holes; main-entry axiom audit complete=$taskProofComplete."
} finally {
    Pop-Location
}
