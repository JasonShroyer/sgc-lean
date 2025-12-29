# export_lean_to_txt.ps1
# Exports all .lean files to .txt format in a separate folder for LLM compatibility

param(
    [string]$OutputFolder = "lean_txt_export"
)

$ProjectRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
$OutputPath = Join-Path $ProjectRoot $OutputFolder

# Clean and recreate output folder
if (Test-Path $OutputPath) {
    Remove-Item -Path $OutputPath -Recurse -Force
}
New-Item -ItemType Directory -Path $OutputPath -Force | Out-Null

# Find all .lean files (excluding .lake and build directories)
$leanFiles = Get-ChildItem -Path $ProjectRoot -Filter "*.lean" -Recurse | 
    Where-Object { $_.FullName -notmatch "\\\.lake\\" -and $_.FullName -notmatch "\\build\\" }

$exportedCount = 0

foreach ($file in $leanFiles) {
    # Calculate relative path from project root
    $relativePath = $file.FullName.Substring($ProjectRoot.Length + 1)
    
    # Change extension to .txt
    $newRelativePath = [System.IO.Path]::ChangeExtension($relativePath, ".txt")
    $destinationPath = Join-Path $OutputPath $newRelativePath
    
    # Create destination directory if needed
    $destinationDir = Split-Path -Parent $destinationPath
    if (-not (Test-Path $destinationDir)) {
        New-Item -ItemType Directory -Path $destinationDir -Force | Out-Null
    }
    
    # Copy file content (preserving UTF-8 without BOM)
    $content = Get-Content -Path $file.FullName -Raw -Encoding UTF8
    [System.IO.File]::WriteAllText($destinationPath, $content, [System.Text.UTF8Encoding]::new($false))
    
    $exportedCount++
    Write-Host "Exported: $relativePath -> $newRelativePath"
}

Write-Host ""
Write-Host "Export complete! $exportedCount files exported to '$OutputFolder/'"
Write-Host "This folder is excluded from Git via .gitignore"
