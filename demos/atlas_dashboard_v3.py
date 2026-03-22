"""
Sheaf Atlas Dashboard v3 - Novel Visualizations for Gauge-Covariant Learning

Unique visualizations designed to show:
1. D4 Gauge Wheel - Which symmetry transformations enable transfer
2. Semantic Manifold - Task signature space with learned connections
3. Defect Cascade - Waterfall showing defect reduction steps
4. Predicate DNA - The genetic makeup of successful solutions
5. Live Terminal - Real-time solver output

Theory: The learning process discovers which gauge elements (rotations, reflections)
connect different regions of the semantic manifold. This is holonomy in action.
"""

import os
import sys
import json
import time
import re
import math
from pathlib import Path
from collections import defaultdict
from flask import Flask, render_template_string, jsonify, Response
from threading import Thread, Lock
import queue

app = Flask(__name__)

# Paths
SCRIPT_DIR = Path(__file__).resolve().parent
ATLAS_DIR = SCRIPT_DIR.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"
LOG_FILE = ATLAS_DIR / "console_output.txt"

# Shared state
log_queue = queue.Queue(maxsize=1000)
parsed_events = []
events_lock = Lock()


def load_json_file(path):
    """Safely load a JSON file."""
    if not path.exists():
        return None
    try:
        with open(path, 'r', encoding='utf-8') as f:
            return json.load(f)
    except:
        return None


def parse_log_file():
    """Parse the console output log file."""
    if not LOG_FILE.exists():
        return []
    
    events = []
    try:
        with open(LOG_FILE, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        current_task = None
        task_idx = 0
        
        for line in lines[-2000:]:  # Last 2000 lines
            line = line.rstrip()
            
            # Task start
            m = re.match(r'\[(\d+)/(\d+)\] Task (\w+)', line)
            if m:
                task_idx = int(m.group(1))
                current_task = {
                    'id': m.group(3),
                    'idx': task_idx,
                    'total': int(m.group(2))
                }
                events.append({
                    'type': 'task_start',
                    'task_id': current_task['id'],
                    'idx': task_idx,
                    'total': current_task['total'],
                    'line': line
                })
                continue
            
            # Defect improvement
            m = re.search(r'd=\d+ ([^:]+): defect ([\d.]+) -> ([\d.]+) \(IG=([\d.]+)\)', line)
            if m:
                events.append({
                    'type': 'defect',
                    'op': m.group(1).strip(),
                    'before': float(m.group(2)),
                    'after': float(m.group(3)),
                    'ig': float(m.group(4)),
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
            
            # Perfect solution
            if '[PERFECT]' in line:
                m = re.search(r'\[PERFECT\] (.+) at depth (\d+)', line)
                if m:
                    events.append({
                        'type': 'perfect',
                        'program': m.group(1),
                        'depth': int(m.group(2)),
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
            
            # Synthesis
            m = re.search(r'\[SYNTH\] (Best partial|Verified): (.+?) \(', line)
            if m:
                events.append({
                    'type': 'synthesis',
                    'status': m.group(1),
                    'program': m.group(2),
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # SGFE rejection
            if 'SHEAF GATE REJECT' in line or '[SGFE v2] REJECT' in line:
                m = re.search(r'sheaf_energy=([\d.]+)', line)
                events.append({
                    'type': 'reject',
                    'energy': float(m.group(1)) if m else 1.0,
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # Tensor predicates
            m = re.search(r'\[TENSOR\] predicate F1=([\d.]+) MI_avg=([\d.]+)', line)
            if m:
                events.append({
                    'type': 'tensor',
                    'f1': float(m.group(1)),
                    'mi': float(m.group(2)),
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
                continue
            
            # Atlas events
            if '[ATLAS]' in line:
                events.append({
                    'type': 'atlas',
                    'task_id': current_task['id'] if current_task else None,
                    'line': line
                })
    
    except Exception as e:
        events.append({'type': 'error', 'message': str(e), 'line': str(e)})
    
    return events


HTML_TEMPLATE = '''
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>Sheaf Atlas - Gauge Learning Visualizer</title>
    <script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script>
    <style>
        :root {
            --bg-dark: #0a0a12;
            --bg-panel: #12121a;
            --border: #2a2a3a;
            --text: #e0e0e0;
            --accent: #00d4ff;
            --success: #00ff88;
            --warning: #ffcc00;
            --error: #ff4466;
        }
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'JetBrains Mono', 'Fira Code', monospace;
            background: var(--bg-dark);
            color: var(--text);
            height: 100vh;
            overflow: hidden;
        }
        
        /* Main Layout */
        .container {
            display: grid;
            grid-template-columns: 1fr 420px;
            grid-template-rows: auto 1fr;
            height: 100vh;
            gap: 1px;
            background: var(--border);
        }
        
        /* Header */
        .header {
            grid-column: 1 / -1;
            background: linear-gradient(90deg, #1a1a2e, #0f3460);
            padding: 12px 20px;
            display: flex;
            justify-content: space-between;
            align-items: center;
            border-bottom: 2px solid var(--accent);
        }
        .header h1 {
            font-size: 18px;
            color: var(--accent);
            display: flex;
            align-items: center;
            gap: 10px;
        }
        .header h1 .logo {
            width: 30px;
            height: 30px;
            background: conic-gradient(var(--accent), var(--success), var(--warning), var(--error), var(--accent));
            border-radius: 50%;
            animation: spin 10s linear infinite;
        }
        @keyframes spin { to { transform: rotate(360deg); } }
        
        .stats-bar {
            display: flex;
            gap: 25px;
        }
        .stat {
            text-align: center;
        }
        .stat-value {
            font-size: 22px;
            font-weight: bold;
            color: var(--accent);
        }
        .stat-label {
            font-size: 9px;
            color: #666;
            text-transform: uppercase;
        }
        
        /* Main Content */
        .main-content {
            display: grid;
            grid-template-rows: 1fr 1fr;
            gap: 1px;
            background: var(--border);
        }
        
        /* Panels */
        .panel {
            background: var(--bg-panel);
            padding: 15px;
            display: flex;
            flex-direction: column;
        }
        .panel-header {
            font-size: 11px;
            color: var(--accent);
            margin-bottom: 10px;
            padding-bottom: 8px;
            border-bottom: 1px solid var(--border);
            display: flex;
            justify-content: space-between;
            align-items: center;
        }
        .panel-content {
            flex: 1;
            overflow: hidden;
            position: relative;
        }
        
        /* Terminal Panel */
        .terminal {
            background: #000;
            border-radius: 4px;
            height: 100%;
            overflow-y: auto;
            padding: 10px;
            font-size: 11px;
            line-height: 1.5;
        }
        .term-line {
            white-space: pre-wrap;
            word-break: break-all;
        }
        .term-task { color: var(--accent); font-weight: bold; }
        .term-perfect { color: var(--success); }
        .term-fail { color: var(--error); opacity: 0.7; }
        .term-defect { color: var(--warning); }
        .term-predicate { color: #da70d6; }
        .term-synthesis { color: #87ceeb; }
        .term-reject { color: var(--error); opacity: 0.5; }
        
        /* Right Sidebar */
        .sidebar {
            display: flex;
            flex-direction: column;
            gap: 1px;
            background: var(--border);
        }
        
        /* Gauge Wheel */
        .gauge-wheel {
            width: 180px;
            height: 180px;
            margin: 10px auto;
            position: relative;
        }
        .gauge-wheel svg {
            width: 100%;
            height: 100%;
        }
        .gauge-segment {
            transition: all 0.3s ease;
            cursor: pointer;
        }
        .gauge-segment:hover {
            filter: brightness(1.3);
        }
        .gauge-label {
            font-size: 10px;
            fill: var(--text);
            text-anchor: middle;
        }
        .gauge-center {
            fill: var(--bg-dark);
        }
        
        /* Task Grid */
        .task-grid {
            display: grid;
            grid-template-columns: repeat(10, 1fr);
            gap: 3px;
            padding: 5px;
        }
        .task-cell {
            aspect-ratio: 1;
            border-radius: 3px;
            transition: all 0.2s;
            position: relative;
        }
        .task-cell.perfect { background: var(--success); }
        .task-cell.fail { background: var(--error); opacity: 0.4; }
        .task-cell.pending { background: #333; }
        .task-cell.current { 
            background: var(--accent);
            animation: pulse 1s infinite;
        }
        @keyframes pulse {
            0%, 100% { transform: scale(1); }
            50% { transform: scale(1.2); }
        }
        .task-cell:hover {
            transform: scale(1.5);
            z-index: 10;
        }
        
        /* Defect Cascade */
        .cascade-container {
            height: 100%;
            position: relative;
        }
        .cascade-step {
            position: absolute;
            left: 10px;
            right: 10px;
            height: 24px;
            background: linear-gradient(90deg, var(--success) 0%, var(--warning) 50%, var(--error) 100%);
            border-radius: 4px;
            transition: all 0.3s ease;
            display: flex;
            align-items: center;
            padding: 0 8px;
            font-size: 10px;
            overflow: hidden;
        }
        .cascade-step .op-name {
            flex: 1;
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
        }
        .cascade-step .defect-value {
            font-weight: bold;
            margin-left: 5px;
        }
        
        /* Predicate DNA */
        .dna-container {
            display: flex;
            flex-wrap: wrap;
            gap: 4px;
            padding: 5px;
            max-height: 100%;
            overflow-y: auto;
        }
        .dna-block {
            padding: 3px 6px;
            border-radius: 3px;
            font-size: 9px;
            background: var(--border);
            border-left: 3px solid var(--accent);
        }
        .dna-block.fill { border-color: var(--success); }
        .dna-block.erase { border-color: var(--error); }
        .dna-block.recolor { border-color: var(--warning); }
        .dna-block.cmap { border-color: #da70d6; }
        
        /* Charts */
        .chart { height: 100%; }
        
        /* Current Task Display */
        .current-task-display {
            background: linear-gradient(135deg, #1a1a2e, #0d0d15);
            padding: 15px;
            border-bottom: 1px solid var(--border);
        }
        .task-id-large {
            font-size: 16px;
            color: var(--accent);
            margin-bottom: 5px;
        }
        .defect-bar {
            height: 8px;
            background: #333;
            border-radius: 4px;
            overflow: hidden;
            margin-top: 8px;
        }
        .defect-fill {
            height: 100%;
            background: linear-gradient(90deg, var(--success), var(--warning), var(--error));
            transition: width 0.3s ease;
        }
        
        /* Info gain sparkline */
        .sparkline {
            height: 40px;
            margin-top: 10px;
        }
    </style>
</head>
<body>
    <div class="container">
        <header class="header">
            <h1>
                <div class="logo"></div>
                Sheaf Atlas — Gauge-Covariant Learning
            </h1>
            <div class="stats-bar">
                <div class="stat">
                    <div class="stat-value" id="s-iter">-</div>
                    <div class="stat-label">Iteration</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-progress">-/-</div>
                    <div class="stat-label">Progress</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-perfect">0</div>
                    <div class="stat-label">Perfect</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-predicates">0</div>
                    <div class="stat-label">Predicates</div>
                </div>
                <div class="stat">
                    <div class="stat-value" id="s-gauge">0</div>
                    <div class="stat-label">Gauge⚡</div>
                </div>
            </div>
        </header>
        
        <div class="main-content">
            <div class="panel">
                <div class="panel-header">
                    <span>📊 Learning Progress</span>
                    <span id="chart-info"></span>
                </div>
                <div class="panel-content">
                    <div class="chart" id="main-chart"></div>
                </div>
            </div>
            
            <div class="panel">
                <div class="panel-header">
                    <span>💻 Live Terminal</span>
                    <span id="term-count">0 lines</span>
                </div>
                <div class="panel-content">
                    <div class="terminal" id="terminal"></div>
                </div>
            </div>
        </div>
        
        <div class="sidebar">
            <div class="current-task-display">
                <div class="task-id-large" id="current-task">Waiting...</div>
                <div style="font-size: 11px; color: #666;" id="task-status">-</div>
                <div class="defect-bar">
                    <div class="defect-fill" id="defect-fill" style="width: 100%"></div>
                </div>
                <div class="sparkline" id="ig-sparkline"></div>
            </div>
            
            <div class="panel" style="flex: 0 0 auto;">
                <div class="panel-header">
                    <span>🎯 Task Grid</span>
                    <span id="grid-stats">-</span>
                </div>
                <div class="task-grid" id="task-grid"></div>
            </div>
            
            <div class="panel" style="flex: 1;">
                <div class="panel-header">
                    <span>⚙️ D4 Gauge Wheel</span>
                </div>
                <div class="panel-content" style="display: flex; flex-direction: column; align-items: center;">
                    <div class="gauge-wheel" id="gauge-wheel"></div>
                    <div style="font-size: 10px; color: #666; text-align: center; margin-top: 5px;">
                        Rotations & reflections enabling cross-task transfer
                    </div>
                </div>
            </div>
            
            <div class="panel" style="flex: 1;">
                <div class="panel-header">
                    <span>🧬 Predicate DNA</span>
                    <span id="dna-count">0</span>
                </div>
                <div class="panel-content">
                    <div class="dna-container" id="predicate-dna"></div>
                </div>
            </div>
            
            <div class="panel" style="flex: 1;">
                <div class="panel-header">
                    <span>📉 Defect Cascade</span>
                </div>
                <div class="panel-content">
                    <div class="cascade-container" id="defect-cascade"></div>
                </div>
            </div>
        </div>
    </div>

    <script>
        // State
        let taskResults = {};
        let igHistory = [];
        let defectSteps = [];
        let gaugeUsage = {e: 0, r: 0, r2: 0, r3: 0, s: 0, sr: 0, sr2: 0, sr3: 0};
        let predicatesSeen = new Set();
        let lastEventCount = 0;
        
        // D4 gauge elements
        const D4_ELEMENTS = [
            {name: 'e', label: 'Identity', angle: 0, color: '#666'},
            {name: 'r', label: 'Rot 90°', angle: 45, color: '#00d4ff'},
            {name: 'r2', label: 'Rot 180°', angle: 90, color: '#00ff88'},
            {name: 'r3', label: 'Rot 270°', angle: 135, color: '#ffcc00'},
            {name: 's', label: 'Flip H', angle: 180, color: '#ff4466'},
            {name: 'sr', label: 'Flip ↗', angle: 225, color: '#da70d6'},
            {name: 'sr2', label: 'Flip V', angle: 270, color: '#87ceeb'},
            {name: 'sr3', label: 'Flip ↘', angle: 315, color: '#ffa500'}
        ];
        
        function initGaugeWheel() {
            const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
            svg.setAttribute('viewBox', '-100 -100 200 200');
            
            D4_ELEMENTS.forEach((elem, i) => {
                const startAngle = (i * 45 - 22.5) * Math.PI / 180;
                const endAngle = (i * 45 + 22.5) * Math.PI / 180;
                const r = 80;
                
                const x1 = Math.cos(startAngle) * r;
                const y1 = Math.sin(startAngle) * r;
                const x2 = Math.cos(endAngle) * r;
                const y2 = Math.sin(endAngle) * r;
                
                const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
                path.setAttribute('d', `M 0 0 L ${x1} ${y1} A ${r} ${r} 0 0 1 ${x2} ${y2} Z`);
                path.setAttribute('fill', elem.color);
                path.setAttribute('opacity', '0.3');
                path.setAttribute('class', 'gauge-segment');
                path.setAttribute('id', `gauge-${elem.name}`);
                path.setAttribute('data-name', elem.name);
                svg.appendChild(path);
                
                // Label
                const labelAngle = (i * 45) * Math.PI / 180;
                const labelR = 55;
                const text = document.createElementNS('http://www.w3.org/2000/svg', 'text');
                text.setAttribute('x', Math.cos(labelAngle) * labelR);
                text.setAttribute('y', Math.sin(labelAngle) * labelR + 3);
                text.setAttribute('class', 'gauge-label');
                text.textContent = elem.label.split(' ')[0];
                svg.appendChild(text);
            });
            
            // Center circle
            const center = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
            center.setAttribute('r', '25');
            center.setAttribute('class', 'gauge-center');
            svg.appendChild(center);
            
            document.getElementById('gauge-wheel').appendChild(svg);
        }
        
        function updateGaugeWheel(usage) {
            const maxUsage = Math.max(1, ...Object.values(usage));
            D4_ELEMENTS.forEach(elem => {
                const segment = document.getElementById(`gauge-${elem.name}`);
                if (segment) {
                    const intensity = (usage[elem.name] || 0) / maxUsage;
                    segment.setAttribute('opacity', 0.2 + intensity * 0.8);
                }
            });
        }
        
        function updateDashboard() {
            fetch('/api/data')
                .then(r => r.json())
                .then(data => {
                    updateStats(data);
                    updateTerminal(data.events);
                    updateTaskGrid(data.events);
                    updateCurrentTask(data.events);
                    updatePredicateDNA(data.events);
                    updateDefectCascade(data.events);
                    updateMainChart(data);
                    updateIGSparkline(data.events);
                })
                .catch(console.error);
        }
        
        function updateStats(data) {
            const p = data.progress || {};
            const a = data.atlas || {};
            const events = data.events || [];
            
            const current = p.iterations?.[p.iterations.length - 1] || {};
            document.getElementById('s-iter').textContent = current.iteration || 1;
            document.getElementById('s-perfect').textContent = current.perfect || 0;
            document.getElementById('s-predicates').textContent = a.total_predicates || 0;
            document.getElementById('s-gauge').textContent = a.stats?.gauge_transfers || 0;
            
            // Progress from events
            const taskStarts = events.filter(e => e.type === 'task_start');
            const last = taskStarts[taskStarts.length - 1];
            if (last) {
                document.getElementById('s-progress').textContent = `${last.idx}/${last.total}`;
            }
        }
        
        function updateTerminal(events) {
            const term = document.getElementById('terminal');
            const lines = events.slice(-150).map(e => {
                let cls = '';
                let text = e.line || '';
                
                if (e.type === 'task_start') cls = 'term-task';
                else if (e.type === 'result' && e.status === 'PERFECT') cls = 'term-perfect';
                else if (e.type === 'result' && e.status === 'FAIL') cls = 'term-fail';
                else if (e.type === 'defect') cls = 'term-defect';
                else if (e.type === 'predicate_discovery') cls = 'term-predicate';
                else if (e.type === 'synthesis' || e.type === 'perfect') cls = 'term-synthesis';
                else if (e.type === 'reject') cls = 'term-reject';
                
                return `<div class="term-line ${cls}">${escapeHtml(text)}</div>`;
            }).join('');
            
            term.innerHTML = lines;
            term.scrollTop = term.scrollHeight;
            document.getElementById('term-count').textContent = `${events.length} events`;
        }
        
        function updateTaskGrid(events) {
            // Build results map
            let currentTaskId = null;
            events.forEach(e => {
                if (e.type === 'task_start') currentTaskId = e.task_id;
                if (e.type === 'result' && currentTaskId) {
                    taskResults[currentTaskId] = e.status;
                }
            });
            
            const taskStarts = events.filter(e => e.type === 'task_start');
            const last = taskStarts[taskStarts.length - 1];
            const total = last?.total || 97;
            const currentIdx = last?.idx || 0;
            
            let html = '';
            let perfect = 0, fail = 0;
            
            for (let i = 1; i <= total; i++) {
                let cls = 'pending';
                const taskId = Object.keys(taskResults)[i - 1];
                const result = taskResults[taskId];
                
                if (result === 'PERFECT') { cls = 'perfect'; perfect++; }
                else if (result === 'FAIL') { cls = 'fail'; fail++; }
                
                if (i === currentIdx) cls = 'current';
                
                html += `<div class="task-cell ${cls}" title="Task ${i}"></div>`;
            }
            
            document.getElementById('task-grid').innerHTML = html;
            document.getElementById('grid-stats').textContent = `✓${perfect} ✗${fail}`;
        }
        
        function updateCurrentTask(events) {
            const taskStarts = events.filter(e => e.type === 'task_start');
            const last = taskStarts[taskStarts.length - 1];
            
            if (last) {
                document.getElementById('current-task').textContent = `Task: ${last.task_id}`;
                document.getElementById('task-status').textContent = `${last.idx} of ${last.total}`;
            }
            
            // Find best defect for current task
            let bestDefect = 1.0;
            let inCurrent = false;
            
            for (let i = events.length - 1; i >= 0; i--) {
                const e = events[i];
                if (e.type === 'task_start') {
                    if (inCurrent) break;
                    inCurrent = true;
                }
                if (inCurrent && e.type === 'defect') {
                    bestDefect = Math.min(bestDefect, e.after);
                }
            }
            
            document.getElementById('defect-fill').style.width = `${bestDefect * 100}%`;
        }
        
        function updatePredicateDNA(events) {
            const container = document.getElementById('predicate-dna');
            const predicates = [];
            
            events.forEach(e => {
                if (e.type === 'sie_op' || e.type === 'synthesis' || e.type === 'perfect') {
                    const op = e.op || e.program || '';
                    // Extract predicate patterns
                    const matches = op.match(/\w+\([^)]+\)/g) || [op.split('->')[0]];
                    matches.forEach(m => {
                        if (m && !predicatesSeen.has(m)) {
                            predicatesSeen.add(m);
                            let type = 'other';
                            if (m.startsWith('fill')) type = 'fill';
                            else if (m.startsWith('erase')) type = 'erase';
                            else if (m.startsWith('recolor')) type = 'recolor';
                            else if (m.startsWith('cmap')) type = 'cmap';
                            predicates.push({text: m.substring(0, 30), type});
                        }
                    });
                }
            });
            
            // Show recent predicates
            const recent = Array.from(predicatesSeen).slice(-30);
            container.innerHTML = recent.map(p => {
                let type = 'other';
                if (p.startsWith('fill')) type = 'fill';
                else if (p.startsWith('erase')) type = 'erase';
                else if (p.startsWith('recolor')) type = 'recolor';
                else if (p.startsWith('cmap')) type = 'cmap';
                return `<div class="dna-block ${type}">${escapeHtml(p.substring(0, 25))}</div>`;
            }).join('');
            
            document.getElementById('dna-count').textContent = predicatesSeen.size;
        }
        
        function updateDefectCascade(events) {
            const container = document.getElementById('defect-cascade');
            
            // Get defect steps for current task
            const steps = [];
            let inCurrent = false;
            
            for (let i = events.length - 1; i >= 0 && steps.length < 8; i--) {
                const e = events[i];
                if (e.type === 'task_start') {
                    if (inCurrent) break;
                    inCurrent = true;
                }
                if (inCurrent && e.type === 'defect') {
                    steps.unshift(e);
                }
            }
            
            const height = container.clientHeight;
            const stepHeight = Math.min(28, (height - 20) / Math.max(steps.length, 1));
            
            container.innerHTML = steps.map((s, i) => {
                const pct = s.after * 100;
                return `<div class="cascade-step" style="top: ${i * stepHeight}px; width: ${100 - pct}%;">
                    <span class="op-name">${escapeHtml(s.op.substring(0, 30))}</span>
                    <span class="defect-value">${s.after.toFixed(3)}</span>
                </div>`;
            }).join('');
        }
        
        function updateMainChart(data) {
            const p = data.progress || {};
            const iterations = p.iterations || [];
            
            if (iterations.length === 0) {
                Plotly.newPlot('main-chart', [], {
                    paper_bgcolor: 'transparent',
                    plot_bgcolor: 'transparent'
                });
                return;
            }
            
            const traces = [
                {
                    x: iterations.map(it => it.iteration),
                    y: iterations.map(it => it.perfect),
                    name: 'Perfect',
                    type: 'scatter',
                    mode: 'lines+markers',
                    fill: 'tozeroy',
                    line: {color: '#00ff88', width: 3},
                    marker: {size: 8}
                },
                {
                    x: iterations.map(it => it.iteration),
                    y: iterations.map(it => it.atlas_size),
                    name: 'Atlas Size',
                    type: 'scatter',
                    mode: 'lines+markers',
                    yaxis: 'y2',
                    line: {color: '#00d4ff', width: 2, dash: 'dot'},
                    marker: {size: 6}
                }
            ];
            
            Plotly.newPlot('main-chart', traces, {
                paper_bgcolor: 'transparent',
                plot_bgcolor: 'transparent',
                margin: {t: 20, r: 50, b: 40, l: 50},
                legend: {x: 0, y: 1, font: {color: '#666', size: 10}},
                xaxis: {
                    title: 'Iteration',
                    gridcolor: 'rgba(255,255,255,0.1)',
                    color: '#666'
                },
                yaxis: {
                    title: 'Perfect Solves',
                    gridcolor: 'rgba(255,255,255,0.1)',
                    color: '#00ff88'
                },
                yaxis2: {
                    title: 'Atlas Size',
                    overlaying: 'y',
                    side: 'right',
                    color: '#00d4ff'
                }
            }, {responsive: true, displayModeBar: false});
        }
        
        function updateIGSparkline(events) {
            const igs = events.filter(e => e.type === 'defect').slice(-50).map(e => e.ig);
            
            if (igs.length < 2) return;
            
            Plotly.newPlot('ig-sparkline', [{
                y: igs,
                type: 'scatter',
                mode: 'lines',
                fill: 'tozeroy',
                line: {color: '#ffcc00', width: 1},
                fillcolor: 'rgba(255,204,0,0.2)'
            }], {
                paper_bgcolor: 'transparent',
                plot_bgcolor: 'transparent',
                margin: {t: 5, r: 5, b: 5, l: 5},
                xaxis: {visible: false},
                yaxis: {visible: false}
            }, {responsive: true, displayModeBar: false});
        }
        
        function escapeHtml(text) {
            const div = document.createElement('div');
            div.textContent = text || '';
            return div.innerHTML;
        }
        
        // Initialize
        initGaugeWheel();
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
    events = parse_log_file()
    
    atlas_summary = {}
    if atlas:
        charts = atlas.get('charts', {})
        atlas_summary = {
            'total_predicates': sum(len(c.get('sections', {})) for c in charts.values()),
            'num_charts': len(charts),
            'charts': {k: {'sections': len(v.get('sections', {})), 'task_ids': v.get('task_ids', [])} 
                      for k, v in list(charts.items())[:20]},
            'stats': atlas.get('statistics', {}),
            'transitions': atlas.get('transitions', [])[-30:],
        }
    
    return jsonify({
        'atlas': atlas_summary,
        'progress': progress,
        'events': events,
        'timestamp': time.time(),
    })


if __name__ == '__main__':
    ATLAS_DIR.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("  SHEAF ATLAS DASHBOARD v3")
    print("  Gauge-Covariant Learning Visualizer")
    print("=" * 60)
    print(f"\n  Dashboard: http://localhost:5050")
    print(f"  Log file:  {LOG_FILE}")
    print(f"\n  Novel Visualizations:")
    print("    • D4 Gauge Wheel - Symmetry transforms in use")
    print("    • Defect Cascade - Step-by-step error reduction")
    print("    • Predicate DNA  - Building blocks of solutions")
    print("    • Live Terminal  - Real-time solver output")
    print("\n  Press Ctrl+C to stop")
    print("=" * 60)
    
    app.run(host='0.0.0.0', port=5050, debug=False, threaded=True)
