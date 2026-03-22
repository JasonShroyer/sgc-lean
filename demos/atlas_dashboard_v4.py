"""
Sheaf Atlas Dashboard v4 - Diagnostic Visualizer

Shows:
1. Current puzzle input/output grids as colored tiles
2. Solver "thinking" state - what operations are being tried
3. Progress indicators - is solver making progress or stuck?
4. Diagnostic insights - why is this task hard?
5. Compute efficiency - learning vs wasted cycles

Theory: If we spend compute, we should learn something. Track:
- Information gained per cycle
- Whether defect is decreasing
- Stuck detection (same operations repeated)
"""

import os
import sys
import json
import time
import re
from pathlib import Path
from collections import defaultdict, Counter
from flask import Flask, render_template_string, jsonify
import colorsys

app = Flask(__name__)

SCRIPT_DIR = Path(__file__).resolve().parent
ATLAS_DIR = SCRIPT_DIR.parent / "data" / "atlas"
ARC_DIR = SCRIPT_DIR.parent / "data" / "arc" / "training"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"
LOG_FILE = ATLAS_DIR / "console_output.txt"

# ARC color palette
ARC_COLORS = [
    '#000000',  # 0: black
    '#0074D9',  # 1: blue
    '#FF4136',  # 2: red
    '#2ECC40',  # 3: green
    '#FFDC00',  # 4: yellow
    '#AAAAAA',  # 5: gray
    '#F012BE',  # 6: magenta
    '#FF851B',  # 7: orange
    '#7FDBFF',  # 8: cyan
    '#B10DC9',  # 9: purple
]


def load_json_file(path):
    if not path.exists():
        return None
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except:
        return None


def load_arc_task(task_id):
    """Load an ARC task by ID."""
    task_file = ARC_DIR / f"{task_id}.json"
    if not task_file.exists():
        return None
    return load_json_file(task_file)


def parse_log_file():
    """Parse console output with diagnostic metrics."""
    if not LOG_FILE.exists():
        return [], {}
    
    events = []
    diagnostics = {
        'current_task': None,
        'defect_history': [],
        'ig_history': [],
        'ops_tried': Counter(),
        'rejections': 0,
        'accepts': 0,
        'stuck_cycles': 0,
        'last_progress_time': time.time(),
        'task_start_time': None,
    }
    
    try:
        with open(LOG_FILE, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        current_task = None
        last_defect = 1.0
        no_progress_count = 0
        
        for line in lines[-3000:]:
            line = line.rstrip()
            
            # Task start
            m = re.match(r'\[(\d+)/(\d+)\] Task (\w+)', line)
            if m:
                current_task = {
                    'id': m.group(3),
                    'idx': int(m.group(1)),
                    'total': int(m.group(2))
                }
                diagnostics['current_task'] = current_task
                diagnostics['defect_history'] = []
                diagnostics['ig_history'] = []
                diagnostics['ops_tried'] = Counter()
                diagnostics['rejections'] = 0
                diagnostics['accepts'] = 0
                diagnostics['task_start_time'] = time.time()
                last_defect = 1.0
                no_progress_count = 0
                events.append({
                    'type': 'task_start',
                    'task_id': current_task['id'],
                    'idx': current_task['idx'],
                    'total': current_task['total'],
                    'line': line
                })
                continue
            
            # Defect improvement
            m = re.search(r'd=\d+ ([^:]+): defect ([\d.]+) -> ([\d.]+) \(IG=([\d.]+)\)', line)
            if m:
                op = m.group(1).strip()
                before = float(m.group(2))
                after = float(m.group(3))
                ig = float(m.group(4))
                
                diagnostics['ops_tried'][op] += 1
                diagnostics['defect_history'].append(after)
                diagnostics['ig_history'].append(ig)
                
                # Check for progress
                if after < last_defect - 0.001:
                    last_defect = after
                    no_progress_count = 0
                    diagnostics['last_progress_time'] = time.time()
                else:
                    no_progress_count += 1
                
                diagnostics['stuck_cycles'] = no_progress_count
                
                events.append({
                    'type': 'defect',
                    'op': op,
                    'before': before,
                    'after': after,
                    'ig': ig,
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # SGFE rejection
            if '[SGFE v2] REJECT' in line or 'SHEAF GATE REJECT' in line:
                diagnostics['rejections'] += 1
                m = re.search(r'sheaf_energy=([\d.]+)', line)
                events.append({
                    'type': 'reject',
                    'energy': float(m.group(1)) if m else 1.0,
                    'task_id': current_task['id'] if current_task else None,
                    'line': line[:100]
                })
                continue
            
            # Perfect
            if '[PERFECT]' in line:
                diagnostics['accepts'] += 1
                events.append({
                    'type': 'perfect',
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # Task result
            m = re.search(r'-> (PERFECT|FAIL|NEAR-MISS) \(defect=([\d.]+)', line)
            if m:
                events.append({
                    'type': 'result',
                    'status': m.group(1),
                    'defect': float(m.group(2)),
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # Predicate discovery
            m = re.search(r'\[IB\] Discovered (\d+) predicates', line)
            if m:
                events.append({
                    'type': 'predicate_discovery',
                    'count': int(m.group(1)),
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # SIE operations
            m = re.search(r'\[SIE-OP\] ([^\(]+) \(NMI=([\d.]+)\)', line)
            if m:
                events.append({
                    'type': 'sie_op',
                    'op': m.group(1).strip(),
                    'nmi': float(m.group(2)),
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
    
    except Exception as e:
        events.append({'type': 'error', 'message': str(e), 'line': str(e)})
    
    return events, diagnostics


def analyze_task_difficulty(task_data):
    """Analyze why a task might be difficult."""
    if not task_data:
        return {'difficulty': 'unknown', 'reasons': []}
    
    reasons = []
    difficulty_score = 0
    
    train = task_data.get('train', [])
    if train:
        ex = train[0]
        inp = ex.get('input', [[]])
        out = ex.get('output', [[]])
        
        h_in, w_in = len(inp), len(inp[0]) if inp else 0
        h_out, w_out = len(out), len(out[0]) if out else 0
        
        # Size complexity
        if h_in * w_in > 200:
            reasons.append(f"Large grid ({h_in}x{w_in})")
            difficulty_score += 2
        
        # Shape change
        if (h_in, w_in) != (h_out, w_out):
            reasons.append(f"Shape change: {h_in}x{w_in} -> {h_out}x{w_out}")
            difficulty_score += 3
        
        # Color diversity
        colors_in = set(c for row in inp for c in row)
        colors_out = set(c for row in out for c in row)
        if len(colors_in) > 5:
            reasons.append(f"Many colors ({len(colors_in)})")
            difficulty_score += 1
        
        # Pattern detection (check for zeros = holes)
        zero_count = sum(1 for row in inp for c in row if c == 0)
        if zero_count > 10:
            reasons.append(f"Pattern inpainting ({zero_count} holes)")
            difficulty_score += 4
        
        # Repeating pattern detection
        if h_in > 8 and w_in > 8:
            # Check if there's a tile pattern
            for period in [2, 3, 4, 5]:
                if h_in % period == 0 or h_in % period <= 1:
                    # Could be tiled
                    reasons.append(f"Possible {period}x{period} tile pattern")
                    difficulty_score += 2
                    break
    
    difficulty = 'easy'
    if difficulty_score >= 6:
        difficulty = 'hard'
    elif difficulty_score >= 3:
        difficulty = 'medium'
    
    return {
        'difficulty': difficulty,
        'score': difficulty_score,
        'reasons': reasons
    }


HTML_TEMPLATE = '''
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Sheaf Atlas v4 - Diagnostic Dashboard</title>
    <script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script>
    <style>
        :root {
            --bg: #0a0a12;
            --panel: #12121a;
            --border: #2a2a3a;
            --text: #e0e0e0;
            --accent: #00d4ff;
            --success: #00ff88;
            --warning: #ffcc00;
            --error: #ff4466;
        }
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'JetBrains Mono', monospace;
            background: var(--bg);
            color: var(--text);
            height: 100vh;
            overflow: hidden;
        }
        .container {
            display: grid;
            grid-template-columns: 350px 1fr 380px;
            grid-template-rows: auto 1fr;
            height: 100vh;
            gap: 1px;
            background: var(--border);
        }
        .header {
            grid-column: 1 / -1;
            background: linear-gradient(90deg, #1a1a2e, #0f3460);
            padding: 10px 20px;
            display: flex;
            justify-content: space-between;
            align-items: center;
            border-bottom: 2px solid var(--accent);
        }
        .header h1 { font-size: 16px; color: var(--accent); }
        .stats-bar { display: flex; gap: 20px; }
        .stat { text-align: center; }
        .stat-value { font-size: 20px; font-weight: bold; color: var(--accent); }
        .stat-label { font-size: 9px; color: #666; }
        
        .panel {
            background: var(--panel);
            padding: 12px;
            display: flex;
            flex-direction: column;
            overflow: hidden;
        }
        .panel-header {
            font-size: 11px;
            color: var(--accent);
            margin-bottom: 8px;
            padding-bottom: 6px;
            border-bottom: 1px solid var(--border);
        }
        .panel-content { flex: 1; overflow: auto; }
        
        /* Puzzle Display */
        .puzzle-container {
            display: flex;
            flex-direction: column;
            gap: 15px;
        }
        .puzzle-pair {
            display: flex;
            gap: 10px;
            align-items: flex-start;
        }
        .puzzle-label {
            font-size: 9px;
            color: #666;
            margin-bottom: 3px;
        }
        .grid-display {
            display: inline-grid;
            gap: 1px;
            background: #333;
            padding: 1px;
            border-radius: 3px;
        }
        .grid-cell {
            width: 12px;
            height: 12px;
            border-radius: 1px;
        }
        
        /* Diagnostic Panel */
        .diagnostic-card {
            background: rgba(0,0,0,0.3);
            border-radius: 6px;
            padding: 10px;
            margin-bottom: 10px;
        }
        .diagnostic-title {
            font-size: 10px;
            color: var(--accent);
            margin-bottom: 6px;
        }
        .difficulty-badge {
            display: inline-block;
            padding: 2px 8px;
            border-radius: 10px;
            font-size: 10px;
            font-weight: bold;
        }
        .difficulty-easy { background: var(--success); color: black; }
        .difficulty-medium { background: var(--warning); color: black; }
        .difficulty-hard { background: var(--error); color: white; }
        
        .reason-list {
            font-size: 10px;
            color: #888;
            margin-top: 5px;
        }
        .reason-item {
            padding: 2px 0;
            border-left: 2px solid var(--warning);
            padding-left: 6px;
            margin-bottom: 3px;
        }
        
        /* Progress Indicator */
        .progress-ring {
            width: 80px;
            height: 80px;
            margin: 10px auto;
        }
        .progress-ring circle {
            fill: none;
            stroke-width: 8;
        }
        .progress-bg { stroke: #333; }
        .progress-fg {
            stroke: var(--accent);
            stroke-linecap: round;
            transform: rotate(-90deg);
            transform-origin: 50% 50%;
            transition: stroke-dashoffset 0.3s;
        }
        .progress-text {
            font-size: 14px;
            fill: var(--text);
            text-anchor: middle;
        }
        
        /* Stuck Indicator */
        .stuck-warning {
            background: rgba(255,68,68,0.2);
            border: 1px solid var(--error);
            border-radius: 6px;
            padding: 10px;
            text-align: center;
            animation: pulse 1s infinite;
        }
        @keyframes pulse {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.6; }
        }
        
        /* Operations Heat Map */
        .ops-heatmap {
            display: flex;
            flex-wrap: wrap;
            gap: 3px;
        }
        .op-chip {
            padding: 2px 6px;
            border-radius: 3px;
            font-size: 9px;
            white-space: nowrap;
        }
        
        /* Terminal */
        .terminal {
            background: #000;
            border-radius: 4px;
            height: 100%;
            overflow-y: auto;
            padding: 8px;
            font-size: 10px;
            line-height: 1.4;
        }
        .term-line { white-space: pre-wrap; word-break: break-all; }
        .term-task { color: var(--accent); font-weight: bold; }
        .term-perfect { color: var(--success); }
        .term-fail { color: var(--error); opacity: 0.7; }
        .term-defect { color: var(--warning); }
        .term-reject { color: var(--error); opacity: 0.5; font-size: 9px; }
        
        /* Charts */
        .chart { height: 150px; }
        
        /* Task Grid */
        .task-grid {
            display: grid;
            grid-template-columns: repeat(10, 1fr);
            gap: 2px;
        }
        .task-cell {
            aspect-ratio: 1;
            border-radius: 2px;
            font-size: 7px;
            display: flex;
            align-items: center;
            justify-content: center;
            cursor: pointer;
        }
        .task-cell.perfect { background: var(--success); }
        .task-cell.fail { background: var(--error); opacity: 0.4; }
        .task-cell.pending { background: #333; }
        .task-cell.current { background: var(--accent); animation: pulse 1s infinite; }
        
        /* Efficiency meter */
        .efficiency-bar {
            height: 6px;
            background: #333;
            border-radius: 3px;
            overflow: hidden;
            margin-top: 5px;
        }
        .efficiency-fill {
            height: 100%;
            transition: width 0.3s;
        }
        .efficiency-good { background: var(--success); }
        .efficiency-medium { background: var(--warning); }
        .efficiency-bad { background: var(--error); }
    </style>
</head>
<body>
    <div class="container">
        <header class="header">
            <h1>🔬 Sheaf Atlas v4 — Diagnostic Dashboard</h1>
            <div class="stats-bar">
                <div class="stat">
                    <div class="stat-value" id="s-progress">-/-</div>
                    <div class="stat-label">Progress</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-perfect">0</div>
                    <div class="stat-label">Perfect</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-efficiency">-</div>
                    <div class="stat-label">Efficiency</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-stuck">-</div>
                    <div class="stat-label">Stuck Cycles</div>
                </div>
            </div>
        </header>
        
        <!-- Left: Puzzle Display -->
        <div class="panel">
            <div class="panel-header">🧩 Current Puzzle</div>
            <div class="panel-content">
                <div class="puzzle-container" id="puzzle-display">
                    <div style="color:#666;text-align:center;">Loading puzzle...</div>
                </div>
                
                <div class="diagnostic-card" style="margin-top:15px;">
                    <div class="diagnostic-title">Task Difficulty Analysis</div>
                    <div id="difficulty-badge"></div>
                    <div class="reason-list" id="difficulty-reasons"></div>
                </div>
            </div>
        </div>
        
        <!-- Center: Terminal + Charts -->
        <div style="display:flex;flex-direction:column;gap:1px;background:var(--border);">
            <div class="panel" style="flex:0 0 200px;">
                <div class="panel-header">📈 Solver Progress</div>
                <div class="panel-content">
                    <div class="chart" id="defect-chart"></div>
                </div>
            </div>
            <div class="panel" style="flex:1;">
                <div class="panel-header">💻 Live Terminal <span id="term-count" style="float:right;color:#666;">0</span></div>
                <div class="panel-content">
                    <div class="terminal" id="terminal"></div>
                </div>
            </div>
        </div>
        
        <!-- Right: Diagnostics -->
        <div style="display:flex;flex-direction:column;gap:1px;background:var(--border);">
            <div class="panel" style="flex:0 0 auto;">
                <div class="panel-header">🎯 Task Grid</div>
                <div class="task-grid" id="task-grid"></div>
            </div>
            
            <div class="panel" style="flex:0 0 auto;">
                <div class="panel-header">⚡ Compute Efficiency</div>
                <div class="panel-content">
                    <div class="diagnostic-card">
                        <div style="display:flex;justify-content:space-between;">
                            <span>Rejections:</span>
                            <span id="d-rejections" style="color:var(--error);">0</span>
                        </div>
                        <div style="display:flex;justify-content:space-between;">
                            <span>Ops Tried:</span>
                            <span id="d-ops">0</span>
                        </div>
                        <div style="display:flex;justify-content:space-between;">
                            <span>Best Defect:</span>
                            <span id="d-best-defect" style="color:var(--success);">1.000</span>
                        </div>
                        <div class="efficiency-bar">
                            <div class="efficiency-fill" id="efficiency-fill" style="width:0%"></div>
                        </div>
                    </div>
                    
                    <div id="stuck-warning" class="stuck-warning" style="display:none;">
                        ⚠️ STUCK: No progress for <span id="stuck-count">0</span> cycles
                    </div>
                </div>
            </div>
            
            <div class="panel" style="flex:1;">
                <div class="panel-header">🔧 Operations Tried</div>
                <div class="panel-content">
                    <div class="ops-heatmap" id="ops-heatmap"></div>
                </div>
            </div>
            
            <div class="panel" style="flex:0 0 150px;">
                <div class="panel-header">📊 Info Gain Distribution</div>
                <div class="panel-content">
                    <div class="chart" id="ig-chart"></div>
                </div>
            </div>
        </div>
    </div>

    <script>
        const ARC_COLORS = ['#000000','#0074D9','#FF4136','#2ECC40','#FFDC00','#AAAAAA','#F012BE','#FF851B','#7FDBFF','#B10DC9'];
        let taskResults = {};
        let currentTaskId = null;
        
        function renderGrid(grid, maxSize=15) {
            if (!grid || !grid.length) return '<div style="color:#666;">No data</div>';
            
            const h = grid.length;
            const w = grid[0].length;
            const cellSize = Math.min(12, Math.floor(180 / Math.max(h, w)));
            
            let html = `<div class="grid-display" style="grid-template-columns:repeat(${w},${cellSize}px);">`;
            for (let r = 0; r < Math.min(h, maxSize); r++) {
                for (let c = 0; c < Math.min(w, maxSize); c++) {
                    const color = ARC_COLORS[grid[r][c]] || '#333';
                    html += `<div class="grid-cell" style="width:${cellSize}px;height:${cellSize}px;background:${color};"></div>`;
                }
            }
            html += '</div>';
            if (h > maxSize || w > maxSize) {
                html += `<div style="font-size:9px;color:#666;">Truncated (${h}x${w})</div>`;
            }
            return html;
        }
        
        function updateDashboard() {
            fetch('/api/data')
                .then(r => r.json())
                .then(data => {
                    updateStats(data);
                    updatePuzzleDisplay(data);
                    updateTerminal(data.events);
                    updateTaskGrid(data.events);
                    updateDiagnostics(data.diagnostics);
                    updateCharts(data);
                    updateOpsHeatmap(data.diagnostics);
                })
                .catch(console.error);
        }
        
        function updateStats(data) {
            const events = data.events || [];
            const diag = data.diagnostics || {};
            
            const taskStarts = events.filter(e => e.type === 'task_start');
            const last = taskStarts[taskStarts.length - 1];
            if (last) {
                document.getElementById('s-progress').textContent = `${last.idx}/${last.total}`;
            }
            
            const perfects = events.filter(e => e.type === 'result' && e.status === 'PERFECT').length;
            document.getElementById('s-perfect').textContent = perfects;
            
            // Efficiency = useful ops / total ops
            const totalOps = Object.values(diag.ops_tried || {}).reduce((a,b) => a+b, 0);
            const rejections = diag.rejections || 0;
            const efficiency = totalOps > 0 ? Math.round((1 - rejections/(totalOps+rejections)) * 100) : 0;
            document.getElementById('s-efficiency').textContent = efficiency + '%';
            
            document.getElementById('s-stuck').textContent = diag.stuck_cycles || 0;
        }
        
        function updatePuzzleDisplay(data) {
            const diag = data.diagnostics || {};
            const task = diag.current_task;
            const taskData = data.task_data;
            
            if (!task || !taskData) {
                document.getElementById('puzzle-display').innerHTML = '<div style="color:#666;">No puzzle loaded</div>';
                return;
            }
            
            currentTaskId = task.id;
            
            const train = taskData.train || [];
            let html = `<div style="font-size:12px;color:var(--accent);margin-bottom:10px;">Task: ${task.id}</div>`;
            
            if (train.length > 0) {
                const ex = train[0];
                html += `
                    <div class="puzzle-pair">
                        <div>
                            <div class="puzzle-label">Input</div>
                            ${renderGrid(ex.input)}
                        </div>
                        <div style="align-self:center;color:#666;">→</div>
                        <div>
                            <div class="puzzle-label">Target</div>
                            ${renderGrid(ex.output)}
                        </div>
                    </div>
                `;
            }
            
            document.getElementById('puzzle-display').innerHTML = html;
            
            // Difficulty analysis
            const analysis = data.task_analysis || {};
            const diffClass = 'difficulty-' + (analysis.difficulty || 'unknown');
            document.getElementById('difficulty-badge').innerHTML = 
                `<span class="difficulty-badge ${diffClass}">${(analysis.difficulty || 'unknown').toUpperCase()}</span>`;
            
            const reasons = analysis.reasons || [];
            document.getElementById('difficulty-reasons').innerHTML = 
                reasons.map(r => `<div class="reason-item">${r}</div>`).join('');
        }
        
        function updateTerminal(events) {
            const term = document.getElementById('terminal');
            const lines = events.slice(-100).map(e => {
                let cls = '';
                let text = e.line || '';
                
                if (e.type === 'task_start') cls = 'term-task';
                else if (e.type === 'result' && e.status === 'PERFECT') cls = 'term-perfect';
                else if (e.type === 'result' && e.status === 'FAIL') cls = 'term-fail';
                else if (e.type === 'defect') cls = 'term-defect';
                else if (e.type === 'reject') { cls = 'term-reject'; text = text.substring(0, 60) + '...'; }
                
                return `<div class="term-line ${cls}">${escapeHtml(text)}</div>`;
            }).join('');
            
            term.innerHTML = lines;
            term.scrollTop = term.scrollHeight;
            document.getElementById('term-count').textContent = events.length;
        }
        
        function updateTaskGrid(events) {
            let currentTaskId = null;
            events.forEach(e => {
                if (e.type === 'task_start') currentTaskId = e.task_id;
                if (e.type === 'result' && currentTaskId) {
                    taskResults[currentTaskId] = e.status;
                }
            });
            
            const taskStarts = events.filter(e => e.type === 'task_start');
            const last = taskStarts[taskStarts.length - 1];
            const total = last?.total || 30;
            const currentIdx = last?.idx || 0;
            
            let html = '';
            for (let i = 1; i <= total; i++) {
                let cls = 'pending';
                const taskId = Object.keys(taskResults)[i - 1];
                const result = taskResults[taskId];
                
                if (result === 'PERFECT') cls = 'perfect';
                else if (result === 'FAIL') cls = 'fail';
                if (i === currentIdx) cls = 'current';
                
                html += `<div class="task-cell ${cls}">${i}</div>`;
            }
            
            document.getElementById('task-grid').innerHTML = html;
        }
        
        function updateDiagnostics(diag) {
            if (!diag) return;
            
            document.getElementById('d-rejections').textContent = diag.rejections || 0;
            
            const totalOps = Object.values(diag.ops_tried || {}).reduce((a,b) => a+b, 0);
            document.getElementById('d-ops').textContent = totalOps;
            
            const defectHistory = diag.defect_history || [];
            const bestDefect = defectHistory.length > 0 ? Math.min(...defectHistory) : 1.0;
            document.getElementById('d-best-defect').textContent = bestDefect.toFixed(4);
            
            // Efficiency bar
            const rejections = diag.rejections || 0;
            const efficiency = totalOps > 0 ? (1 - rejections/(totalOps+rejections)) : 0;
            const effFill = document.getElementById('efficiency-fill');
            effFill.style.width = (efficiency * 100) + '%';
            effFill.className = 'efficiency-fill ' + 
                (efficiency > 0.5 ? 'efficiency-good' : efficiency > 0.2 ? 'efficiency-medium' : 'efficiency-bad');
            
            // Stuck warning
            const stuckWarning = document.getElementById('stuck-warning');
            const stuckCycles = diag.stuck_cycles || 0;
            if (stuckCycles > 50) {
                stuckWarning.style.display = 'block';
                document.getElementById('stuck-count').textContent = stuckCycles;
            } else {
                stuckWarning.style.display = 'none';
            }
        }
        
        function updateCharts(data) {
            const diag = data.diagnostics || {};
            const defectHistory = diag.defect_history || [];
            const igHistory = diag.ig_history || [];
            
            // Defect chart
            if (defectHistory.length > 0) {
                Plotly.newPlot('defect-chart', [{
                    y: defectHistory.slice(-100),
                    type: 'scatter',
                    mode: 'lines',
                    fill: 'tozeroy',
                    line: {color: '#00d4ff', width: 2},
                    fillcolor: 'rgba(0,212,255,0.2)'
                }], {
                    paper_bgcolor: 'transparent',
                    plot_bgcolor: 'transparent',
                    margin: {t: 10, r: 10, b: 30, l: 40},
                    xaxis: {title: 'Step', color: '#666', gridcolor: 'rgba(255,255,255,0.1)'},
                    yaxis: {title: 'Defect', color: '#666', gridcolor: 'rgba(255,255,255,0.1)', range: [0, 1]}
                }, {responsive: true, displayModeBar: false});
            }
            
            // IG histogram
            if (igHistory.length > 0) {
                Plotly.newPlot('ig-chart', [{
                    x: igHistory.slice(-100),
                    type: 'histogram',
                    marker: {color: '#ffcc00'},
                    nbinsx: 20
                }], {
                    paper_bgcolor: 'transparent',
                    plot_bgcolor: 'transparent',
                    margin: {t: 5, r: 5, b: 25, l: 30},
                    xaxis: {title: 'IG', color: '#666', titlefont: {size: 10}},
                    yaxis: {color: '#666'}
                }, {responsive: true, displayModeBar: false});
            }
        }
        
        function updateOpsHeatmap(diag) {
            const ops = diag?.ops_tried || {};
            const container = document.getElementById('ops-heatmap');
            
            const sorted = Object.entries(ops).sort((a,b) => b[1] - a[1]).slice(0, 20);
            const maxCount = sorted.length > 0 ? sorted[0][1] : 1;
            
            container.innerHTML = sorted.map(([op, count]) => {
                const intensity = count / maxCount;
                const hue = 200 - intensity * 200; // Blue to red
                return `<div class="op-chip" style="background:hsl(${hue},70%,30%);" title="${op}: ${count}x">
                    ${op.substring(0, 15)}${op.length > 15 ? '...' : ''} (${count})
                </div>`;
            }).join('');
        }
        
        function escapeHtml(text) {
            const div = document.createElement('div');
            div.textContent = text || '';
            return div.innerHTML;
        }
        
        updateDashboard();
        setInterval(updateDashboard, 1500);
    </script>
</body>
</html>
'''


@app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE)


@app.route('/api/data')
def api_data():
    atlas = load_json_file(ATLAS_FILE)
    progress = load_json_file(PROGRESS_FILE)
    events, diagnostics = parse_log_file()
    
    # Load current task data
    task_data = None
    task_analysis = None
    if diagnostics.get('current_task'):
        task_id = diagnostics['current_task']['id']
        task_data = load_arc_task(task_id)
        task_analysis = analyze_task_difficulty(task_data)
    
    atlas_summary = {}
    if atlas:
        charts = atlas.get('charts', {})
        atlas_summary = {
            'total_predicates': sum(len(c.get('sections', {})) for c in charts.values()),
            'num_charts': len(charts),
            'stats': atlas.get('statistics', {}),
        }
    
    return jsonify({
        'atlas': atlas_summary,
        'progress': progress,
        'events': events,
        'diagnostics': diagnostics,
        'task_data': task_data,
        'task_analysis': task_analysis,
        'timestamp': time.time(),
    })


if __name__ == '__main__':
    ATLAS_DIR.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("  SHEAF ATLAS DASHBOARD v4 - Diagnostic Visualizer")
    print("=" * 60)
    print(f"\n  Dashboard: http://localhost:5050")
    print(f"\n  Features:")
    print("    - Puzzle visualization (input -> target)")
    print("    - Task difficulty analysis")
    print("    - Stuck detection & efficiency metrics")
    print("    - Operations heatmap")
    print("    - Real-time defect tracking")
    print("\n  Press Ctrl+C to stop")
    print("=" * 60)
    
    app.run(host='0.0.0.0', port=5050, debug=False, threaded=True)
