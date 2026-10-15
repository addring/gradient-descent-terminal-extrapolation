param([switch]$SkipBuild)
$ErrorActionPreference = 'Stop'
Push-Location -LiteralPath $PSScriptRoot
try {
    $taskOutput = 'verification/current_complete'
    New-Item -ItemType Directory -Path $taskOutput -Force | Out-Null
    $taskDate = Get-Date -Format 'yyyy-MM-dd'
    # Remove nested Lean comments and strings before checking proof shortcuts.
    function Remove-TaskLeanComments([string]$taskInput) {
        $taskResult = [System.Text.StringBuilder]::new()
        $taskDepth = 0
        $taskString = $false
        $taskIndex = 0
        while ($taskIndex -lt $taskInput.Length) {
            $taskChar = $taskInput[$taskIndex]
            $taskPair = ''
            if ($taskIndex + 1 -lt $taskInput.Length) { $taskPair = $taskInput.Substring($taskIndex, 2) }
            if ($taskDepth -gt 0) {
                if ($taskPair -eq '/-') { $taskDepth++; $taskIndex += 2; continue }
                if ($taskPair -eq '-/') { $taskDepth--; $taskIndex += 2; continue }
                if ($taskChar -eq "`n") { [void]$taskResult.Append("`n") }
                $taskIndex++; continue
            }
            if ($taskString) {
                if ($taskChar -eq '\') { $taskIndex += 2; continue }
                if ($taskChar -eq '"') { $taskString = $false }
                $taskIndex++; continue
            }
            if ($taskPair -eq '/-') { $taskDepth = 1; [void]$taskResult.Append(' '); $taskIndex += 2; continue }
            if ($taskPair -eq '--') {
                while ($taskIndex -lt $taskInput.Length -and $taskInput[$taskIndex] -ne "`n") { $taskIndex++ }
                continue
            }
            if ($taskChar -eq '"') { $taskString = $true; [void]$taskResult.Append(' '); $taskIndex++; continue }
            [void]$taskResult.Append($taskChar)
            $taskIndex++
        }
        if ($taskDepth -ne 0 -or $taskString) { throw 'Unterminated Lean comment or string.' }
        return $taskResult.ToString()
    }
    $taskModuleFiles = @(Get-ChildItem -LiteralPath 'CriticalExtrapolation', 'PaperFramework' -Filter '*.lean' | Sort-Object FullName)
    $taskRootFiles = @(Get-ChildItem -LiteralPath '.' -Filter '*.lean' | Sort-Object Name)
    foreach ($taskFile in @($taskModuleFiles) + @($taskRootFiles)) {
        $taskCode = Remove-TaskLeanComments (Get-Content -LiteralPath $taskFile.FullName -Raw -Encoding utf8)
        if ($taskCode -match '\b(sorry|sorryAx|admit|axiom|unsafe|native_decide)\b') {
            throw "Unfinished or forbidden proof shortcut in $($taskFile.Name)."
        }
    }
    $taskImports = @('import CriticalExtrapolation', 'import PaperFramework', 'import OriginalExtension')
    $taskTheorems = @()
    foreach ($taskFile in $taskModuleFiles) {
        $taskDirectory = Split-Path -Leaf $taskFile.DirectoryName
        $taskImports += 'import ' + $taskDirectory + '.' + $taskFile.BaseName
        $taskCode = Remove-TaskLeanComments (Get-Content -LiteralPath $taskFile.FullName -Raw -Encoding utf8)
        $taskNamespace = [regex]::Match($taskCode, '(?m)^namespace\s+(\S+)').Groups[1].Value
        foreach ($taskMatch in [regex]::Matches($taskCode, "(?m)^theorem\s+([\w'.]+)")) {
            $taskTheorems += $taskNamespace + '.' + $taskMatch.Groups[1].Value
        }
    }
    $taskUniqueNames = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
    foreach ($taskName in $taskTheorems) {
        if (-not $taskUniqueNames.Add($taskName)) { throw "Duplicate theorem inventory: $taskName" }
    }
    $taskAuditSource = ($taskImports -join "`n") + "`n`n" +
        (($taskTheorems | ForEach-Object { '#print axioms ' + $_ }) -join "`n") + "`n"
    Set-Content -LiteralPath "$taskOutput/CompleteAudit.lean" -Value $taskAuditSource -Encoding utf8
    if (-not $SkipBuild) {
        & lake build
        if ($LASTEXITCODE -ne 0) { throw 'Separate complete-project build failed.' }
    }
    $taskAudit = & lake env lean "$taskOutput/CompleteAudit.lean" 2>&1
    if ($LASTEXITCODE -ne 0) { throw ($taskAudit -join "`n") }
    $taskAuditText = $taskAudit -join "`n"
    $taskEntries = [regex]::Matches($taskAuditText,
        "'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
    if ($taskEntries.Count -ne $taskTheorems.Count) { throw 'Complete audit entry count mismatch.' }
    $taskAllowed = @('propext', 'Classical.choice', 'Quot.sound')
    foreach ($taskEntry in $taskEntries) {
        if ($taskEntry.Groups[1].Value -notin $taskTheorems) { throw 'Unexpected audit theorem.' }
        foreach ($taskAxiom in ($taskEntry.Groups[2].Value -split ',')) {
            if ($taskAxiom.Trim() -and $taskAxiom.Trim() -notin $taskAllowed) {
                throw "Unexpected axiom: $($taskAxiom.Trim())"
            }
        }
    }
    foreach ($taskTheorem in $taskTheorems) {
        if (-not $taskAuditText.Contains("'$taskTheorem'")) { throw "Missing complete audit: $taskTheorem" }
    }
    $taskAudit | Set-Content -LiteralPath "$taskOutput/axioms.txt" -Encoding utf8
    [ordered]@{
        date = $taskDate
        audited_theorems = $taskTheorems.Count
        direct_sorry_count = 0
        sorryAx = $false
        allowed_axioms = $taskAllowed
        main_theorem = 'CriticalExtrapolation.Paper.original_sharp_critical_scale'
        critical_definition = 'CriticalExtrapolation.Paper.originalCriticalCoefficient'
        separate_full_build = (-not $SkipBuild)
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath "$taskOutput/summary.json" -Encoding utf8
    $taskManifestFiles = @($taskModuleFiles | ForEach-Object { (Split-Path -Leaf $_.DirectoryName) + '/' + $_.Name })
    $taskManifestFiles += @('CriticalExtrapolation.lean', 'PaperFramework.lean', 'OriginalExtension.lean', 'OriginalAudit.lean',
        "$taskOutput/CompleteAudit.lean", 'check_complete.ps1',
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
    [ordered]@{
        date = $taskDate
        scope = 'Every source theorem in CriticalExtrapolation and PaperFramework, including the equality-set critical-scale theorem'
        files = @($taskManifestFiles | ForEach-Object {
            [ordered]@{ path = $_; sha256 = (Get-FileHash -LiteralPath $_ -Algorithm SHA256).Hash.ToLowerInvariant() }
        })
    } | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath "$taskOutput/source_manifest.json" -Encoding utf8
    Write-Output "Complete audit passed: $($taskTheorems.Count) theorems, zero proof holes, standard axioms only."
} finally {
    Pop-Location
}
