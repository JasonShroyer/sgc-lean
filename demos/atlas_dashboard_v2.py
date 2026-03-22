"""
Enhanced Sheaf Atlas Dashboard v2

Rich real-time visualization showing:
1. Live log stream from evaluation
2. Per-puzzle defect reduction timeline
3. Predicate discovery events
4. Synthesis beam visualization
5. Information gain heatmap
6. Task difficulty landscape

Usage:
  python atlas_dashboard_v2.py
  
Then open http://localhost:5050 in your browser.
"""

import os
import json
import time
import re
from pathlib import Path
from collections import defaultdict
from flask import Flask, render_template_string, jsonify
from threading import Lock

app = Flask(__name__)

ATLAS_DIR = Path(__file__).resolve().parent.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"
LOG_FILE = ATLAS_DIR / "eval_log.jsonl"

# In-memory state for real-time updates
state_lock = Lock()
current_state = {
    'current_task': None,
    'task_history': [],
    'events': [],
    'defect_timeline': [],
    'predicates_discovered': [],
    'synthesis_steps': [],
}


def load_atlas():
    if not ATLAS_FILE.exists():
        return None
    try:
        with open(ATLAS_FILE, 'r') as f:
            return json.load(f)
    except:
        return None


def load_progress():
    if not PROGRESS_FILE.exists():
        return None
    try:
        with open(PROGRESS_FILE, 'r') as f:
            return json.load(f)
    except:
        return None


def load_log_events():
    """Load structured log events."""
    if not LOG_FILE.exists():
        return []
    events = []
    try:
        with open(LOG_FILE, 'r') as f:
            for line in f:
                try:
                    events.append(json.loads(line.strip()))
                except:
                    pass
    except:
        pass
    return events[-500:]  # Last 500 events


def parse_console_output():
    """Parse the console output file if it exists."""
    log_path = ATLAS_DIR / "console_output.txt"
    if not log_path.exists():
        return []
    
    events = []
    try:
        with open(log_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
        
        # Parse different event types
        lines = content.split('\n')
        current_task = None
        
        for line in lines[-1000:]:  # Last 1000 lines
            # Task start
            m = re.match(r'\[(\d+)/(\d+)\] Task (\w+)', line)
            if m:
                current_task = {
                    'idx': int(m.group(1)),
                    'total': int(m.group(2)),
                    'task_id': m.group(3),
                    'events': []
                }
                events.append({'type': 'task_start', 'task': current_task})
                continue
            
            # Defect improvement
            m = re.search(r'd=\d+ (\S+): defect ([\d.]+) -> ([\d.]+) \(IG=([\d.]+)\)', line)
            if m:
                events.append({
                    'type': 'defect_improvement',
                    'op': m.group(1),
                    'before': float(m.group(2)),
                    'after': float(m.group(3)),
                    'ig': float(m.group(4)),
                    'task_id': current_task['task_id'] if current_task else None
                })
                continue
            
            # Predicate discovery
            if '[IB] Discovered' in line:
                m = re.search(r'\[IB\] Discovered (\d+) predicates', line)
                if m:
                    events.append({
                        'type': 'predicate_discovery',
                        'count': int(m.group(1)),
                        'method': 'Information Bottleneck',
                        'task_id': current_task['task_id'] if current_task else None
                    })
                continue
            
            # SIE operations
            if '[SIE-OP]' in line:
                m = re.search(r'\[SIE-OP\] (\S+) \(NMI=([\d.]+)\)', line)
                if m:
                    events.append({
                        'type': 'sie_op',
                        'op': m.group(1),
                        'nmi': float(m.group(2)),
                        'task_id': current_task['task_id'] if current_task else None
                    })
                continue
            
            # Perfect solution
            if '[PERFECT]' in line or '-> PERFECT' in line:
                events.append({
                    'type': 'perfect',
                    'task_id': current_task['task_id'] if current_task else None,
                    'line': line[:100]
                })
                continue
            
            # Synthesis best partial
            if '[SYNTH] Best partial' in line:
                m = re.search(r'\[SYNTH\] Best partial: (.+) \(avg_defect=([\d.]+)\)', line)
                if m:
                    events.append({
                        'type': 'synthesis',
                        'program': m.group(1),
                        'defect': float(m.group(2)),
                        'task_id': current_task['task_id'] if current_task else None
                    })
                continue
            
            # SGFE rejections (sheaf gate)
            if 'SHEAF GATE REJECT' in line:
                m = re.search(r'sheaf_energy=([\d.]+)', line)
                events.append({
                    'type': 'sheaf_reject',
                    'energy': float(m.group(1)) if m else 1.0,
                    'task_id': current_task['task_id'] if current_task else None
                })
                continue
            
            # Tensor predicates
            if '[TENSOR] predicate' in line:
                m = re.search(r'F1=([\d.]+) MI_avg=([\d.]+)', line)
                if m:
                    events.append({
                        'type': 'tensor_pred',
                        'f1': float(m.group(1)),
                        'mi': float(m.group(2)),
                        'task_id': current_task['task_id'] if current_task else None
                    })
                continue
            
            # Atlas events
            if '[ATLAS]' in line:
                events.append({
                    'type': 'atlas',
                    'message': line,
                    'task_id': current_task['task_id'] if current_task else None
                })
                continue
            
            # Task result
            if '-> FAIL' in line or '-> PERFECT' in line or '-> NEAR-MISS' in line:
                result = 'FAIL'
                if 'PERFECT' in line: result = 'PERFECT'
                elif 'NEAR-MISS' in line: result = 'NEAR-MISS'
                m = re.search(r'defect=([\d.]+)', line)
                events.append({
                    'type': 'task_result',
                    'result': result,
                    'defect': float(m.group(1)) if m else 1.0,
                    'task_id': current_task['task_id'] if current_task else None
                })
    except Exception as e:
        events.append({'type': 'error', 'message': str(e)})
    
    return events


HTML_TEMPLATE = '''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Sheaf Atlas Dashboard v2</title>
    <script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'SF Mono', 'Fira Code', monospace;
            background: #0a0a0f;
            color: #e0e0e0;
            min-height: 100vh;
        }
        .header {
            background: linear-gradient(90deg, #1a1a2e 0%, #0f3460 100%);
            padding: 15px 20px;
            display: flex;
            justify-content: space-between;
            align-items: center;
            border-bottom: 2px solid #00d4ff;
        }
        .header h1 { font-size: 20px; color: #00d4ff; }
        .header-stats {
            display: flex;
            gap: 30px;
        }
        .header-stat {
            text-align: center;
        }
        .header-stat .value {
            font-size: 24px;
            font-weight: bold;
            color: #00d4ff;
        }
        .header-stat .label {
            font-size: 10px;
            color: #666;
        }
        .main-grid {
            display: grid;
            grid-template-columns: 1fr 400px;
            height: calc(100vh - 60px);
        }
        .left-panel {
            display: grid;
            grid-template-rows: 1fr 1fr;
            gap: 1px;
            background: #1a1a2e;
        }
        .panel {
            background: #0d0d15;
            padding: 15px;
            overflow: hidden;
            display: flex;
            flex-direction: column;
        }
        .panel-title {
            font-size: 12px;
            color: #00d4ff;
            margin-bottom: 10px;
            padding-bottom: 5px;
            border-bottom: 1px solid #1a1a2e;
            display: flex;
            justify-content: space-between;
        }
        .panel-content {
            flex: 1;
            overflow: hidden;
        }
        .log-stream {
            height: 100%;
            overflow-y: auto;
            font-size: 11px;
            line-height: 1.4;
        }
        .log-line {
            padding: 3px 8px;
            border-left: 3px solid transparent;
            margin-bottom: 2px;
        }
        .log-line.task-start {
            background: rgba(0,212,255,0.1);
            border-color: #00d4ff;
            font-weight: bold;
        }
        .log-line.perfect {
            background: rgba(0,255,100,0.2);
            border-color: #00ff64;
            color: #00ff64;
        }
        .log-line.fail {
            background: rgba(255,100,100,0.1);
            border-color: #ff6464;
        }
        .log-line.defect {
            color: #ffd700;
        }
        .log-line.predicate {
            color: #da70d6;
        }
        .log-line.synthesis {
            color: #87ceeb;
        }
        .log-line.atlas {
            color: #ff6b6b;
        }
        .log-line.sheaf-reject {
            color: #ff4444;
            opacity: 0.7;
        }
        .right-panel {
            background: #0d0d15;
            border-left: 1px solid #1a1a2e;
            display: flex;
            flex-direction: column;
        }
        .current-task {
            padding: 15px;
            background: linear-gradient(180deg, #1a1a2e 0%, #0d0d15 100%);
            border-bottom: 1px solid #1a1a2e;
        }
        .task-id {
            font-size: 18px;
            color: #00d4ff;
            margin-bottom: 5px;
        }
        .task-progress {
            font-size: 12px;
            color: #666;
        }
        .defect-meter {
            margin-top: 10px;
            height: 20px;
            background: #1a1a2e;
            border-radius: 10px;
            overflow: hidden;
            position: relative;
        }
        .defect-fill {
            height: 100%;
            background: linear-gradient(90deg, #00ff64 0%, #ffd700 50%, #ff4444 100%);
            transition: width 0.3s ease;
        }
        .defect-label {
            position: absolute;
            width: 100%;
            text-align: center;
            line-height: 20px;
            font-size: 11px;
            color: white;
            text-shadow: 1px 1px 2px black;
        }
        .event-timeline {
            flex: 1;
            overflow-y: auto;
            padding: 10px;
        }
        .event {
            padding: 8px 12px;
            margin-bottom: 8px;
            border-radius: 6px;
            font-size: 11px;
        }
        .event.defect-improvement {
            background: linear-gradient(90deg, rgba(0,255,100,0.2), transparent);
            border-left: 3px solid #00ff64;
        }
        .event.predicate-discovery {
            background: linear-gradient(90deg, rgba(218,112,214,0.2), transparent);
            border-left: 3px solid #da70d6;
        }
        .event.synthesis {
            background: linear-gradient(90deg, rgba(135,206,235,0.2), transparent);
            border-left: 3px solid #87ceeb;
        }
        .event.sheaf-reject {
            background: linear-gradient(90deg, rgba(255,68,68,0.1), transparent);
            border-left: 3px solid #ff4444;
        }
        .event-op { color: #00d4ff; font-weight: bold; }
        .event-value { color: #ffd700; }
        .event-delta { color: #00ff64; }
        .chart-small { height: 150px; }
        .task-grid {
            display: grid;
            grid-template-columns: repeat(20, 1fr);
            gap: 2px;
            padding: 10px;
        }
        .task-cell {
            aspect-ratio: 1;
            border-radius: 2px;
            cursor: pointer;
            transition: transform 0.1s;
        }
        .task-cell:hover { transform: scale(1.5); z-index: 10; }
        .task-cell.perfect { background: #00ff64; }
        .task-cell.near-miss { background: #ffd700; }
        .task-cell.fail { background: #ff4444; opacity: 0.5; }
        .task-cell.pending { background: #333; }
        .task-cell.current { background: #00d4ff; animation: pulse 1s infinite; }
        @keyframes pulse {
            0%, 100% { opacity: 1; }
            50% { opacity: 0.5; }
        }
        .info-gain-chart { height: 200px; }
        .stats-row {
            display: flex;
            gap: 10px;
            padding: 10px;
            background: #1a1a2e;
        }
        .mini-stat {
            flex: 1;
            text-align: center;
            padding: 8px;
            background: #0d0d15;
            border-radius: 4px;
        }
        .mini-stat .value { font-size: 18px; color: #00d4ff; }
        .mini-stat .label { font-size: 9px; color: #666; }
    </style>
</head>
<body>
    <div class="header">
        <h1>🧠 Sheaf Atlas — Model Thinking Visualizer</h1>
        <div class="header-stats">
            <div class="header-stat">
                <div class="value" id="h-iteration">-</div>
                <div class="label">ITERATION</div>
            </div>
            <div class="header-stat">
                <div class="value" id="h-progress">-/-</div>
                <div class="label">PROGRESS</div>
            </div>
            <div class="header-stat">
                <div class="value" id="h-perfect">0</div>
                <div class="label">PERFECT</div>
            </div>
            <div class="header-stat">
                <div class="value" id="h-predicates">0</div>
                <div class="label">PREDICATES</div>
            </div>
            <div class="header-stat">
                <div class="value" id="h-gauge">0</div>
                <div class="label">GAUGE TRANSFERS</div>
            </div>
        </div>
    </div>
    
    <div class="main-grid">
        <div class="left-panel">
            <div class="panel">
                <div class="panel-title">
                    <span>📊 Task Progress Grid</span>
                    <span id="grid-summary">-</span>
                </div>
                <div class="panel-content">
                    <div class="task-grid" id="task-grid"></div>
                    <div class="info-gain-chart" id="ig-chart"></div>
                </div>
            </div>
            <div class="panel">
                <div class="panel-title">
                    <span>📜 Live Log Stream</span>
                    <span id="log-count">0 events</span>
                </div>
                <div class="panel-content">
                    <div class="log-stream" id="log-stream"></div>
                </div>
            </div>
        </div>
        
        <div class="right-panel">
            <div class="current-task">
                <div class="task-id" id="current-task-id">Waiting for task...</div>
                <div class="task-progress" id="current-task-progress"></div>
                <div class="defect-meter">
                    <div class="defect-fill" id="defect-fill" style="width: 100%"></div>
                    <div class="defect-label" id="defect-label">Defect: 1.000</div>
                </div>
            </div>
            
            <div class="stats-row">
                <div class="mini-stat">
                    <div class="value" id="s-ig">-</div>
                    <div class="label">Best IG</div>
                </div>
                <div class="mini-stat">
                    <div class="value" id="s-depth">-</div>
                    <div class="label">Depth</div>
                </div>
                <div class="mini-stat">
                    <div class="value" id="s-preds">-</div>
                    <div class="label">Preds</div>
                </div>
            </div>
            
            <div class="panel-title" style="padding: 10px;">⚡ Event Timeline</div>
            <div class="event-timeline" id="event-timeline"></div>
            
            <div class="panel" style="max-height: 200px;">
                <div class="panel-title">📈 Defect Over Time</div>
                <div class="chart-small" id="defect-chart"></div>
            </div>
        </div>
    </div>
    
    <script>
        let taskResults = {};
        let currentTask = null;
        let defectHistory = [];
        let igHistory = [];
        
        function updateDashboard() {
            fetch('/api/data')
                .then(r => r.json())
                .then(data => {
                    updateHeader(data);
                    updateTaskGrid(data);
                    updateLogStream(data);
                    updateEventTimeline(data);
                    updateCurrentTask(data);
                    updateCharts(data);
                })
                .catch(console.error);
        }
        
        function updateHeader(data) {
            const p = data.progress || {};
            const a = data.atlas || {};
            const events = data.events || [];
            
            const current = p.iterations?.[p.iterations.length - 1] || {};
            document.getElementById('h-iteration').textContent = current.iteration || 1;
            document.getElementById('h-perfect').textContent = current.perfect || 0;
            document.getElementById('h-predicates').textContent = a.total_predicates || 0;
            document.getElementById('h-gauge').textContent = a.stats?.gauge_transfers || 0;
            
            // Calculate progress from events
            const taskStarts = events.filter(e => e.type === 'task_start');
            const lastTask = taskStarts[taskStarts.length - 1];
            if (lastTask) {
                document.getElementById('h-progress').textContent = 
                    `${lastTask.task?.idx || 0}/${lastTask.task?.total || 97}`;
            }
        }
        
        function updateTaskGrid(data) {
            const events = data.events || [];
            const grid = document.getElementById('task-grid');
            
            // Build task results map
            let lastTaskId = null;
            events.forEach(e => {
                if (e.type === 'task_start') lastTaskId = e.task?.task_id;
                if (e.type === 'task_result' && lastTaskId) {
                    taskResults[lastTaskId] = e.result;
                }
            });
            
            // Find current task
            const taskStarts = events.filter(e => e.type === 'task_start');
            const lastStart = taskStarts[taskStarts.length - 1];
            currentTask = lastStart?.task?.task_id;
            
            // Render grid (assume 97 tasks)
            const total = lastStart?.task?.total || 97;
            let html = '';
            let perfect = 0, fail = 0, pending = 0;
            
            for (let i = 0; i < total; i++) {
                const taskId = Object.keys(taskResults)[i] || `task_${i}`;
                const result = taskResults[taskId];
                let cls = 'pending';
                if (result === 'PERFECT') { cls = 'perfect'; perfect++; }
                else if (result === 'NEAR-MISS') { cls = 'near-miss'; }
                else if (result === 'FAIL') { cls = 'fail'; fail++; }
                else { pending++; }
                
                if (i === (lastStart?.task?.idx - 1)) cls = 'current';
                
                html += `<div class="task-cell ${cls}" title="${taskId}: ${result || 'pending'}"></div>`;
            }
            grid.innerHTML = html;
            
            document.getElementById('grid-summary').textContent = 
                `✓${perfect} ✗${fail} ○${pending}`;
        }
        
        function updateLogStream(data) {
            const events = data.events || [];
            const stream = document.getElementById('log-stream');
            
            let html = '';
            events.slice(-100).forEach(e => {
                let cls = '';
                let text = '';
                
                switch(e.type) {
                    case 'task_start':
                        cls = 'task-start';
                        text = `[${e.task?.idx}/${e.task?.total}] Task ${e.task?.task_id}`;
                        break;
                    case 'defect_improvement':
                        cls = 'defect';
                        text = `  ↓ ${e.op}: ${e.before.toFixed(4)} → ${e.after.toFixed(4)} (IG=${e.ig.toFixed(4)})`;
                        break;
                    case 'predicate_discovery':
                        cls = 'predicate';
                        text = `  🔬 Discovered ${e.count} predicates via ${e.method}`;
                        break;
                    case 'sie_op':
                        cls = 'synthesis';
                        text = `  ⚙️ SIE: ${e.op} (NMI=${e.nmi.toFixed(4)})`;
                        break;
                    case 'synthesis':
                        cls = 'synthesis';
                        text = `  🔧 Best: ${e.program} (defect=${e.defect.toFixed(4)})`;
                        break;
                    case 'perfect':
                        cls = 'perfect';
                        text = `  ✅ PERFECT SOLUTION FOUND!`;
                        break;
                    case 'task_result':
                        cls = e.result === 'PERFECT' ? 'perfect' : 'fail';
                        text = `  → ${e.result} (defect=${e.defect.toFixed(4)})`;
                        break;
                    case 'sheaf_reject':
                        cls = 'sheaf-reject';
                        text = `  ✗ Sheaf reject: energy=${e.energy.toFixed(3)}`;
                        break;
                    case 'atlas':
                        cls = 'atlas';
                        text = `  ${e.message.substring(0, 80)}`;
                        break;
                    case 'tensor_pred':
                        cls = 'predicate';
                        text = `  📊 Tensor pred: F1=${e.f1.toFixed(3)} MI=${e.mi.toFixed(4)}`;
                        break;
                }
                
                if (text) {
                    html += `<div class="log-line ${cls}">${escapeHtml(text)}</div>`;
                }
            });
            
            stream.innerHTML = html;
            stream.scrollTop = stream.scrollHeight;
            
            document.getElementById('log-count').textContent = `${events.length} events`;
        }
        
        function updateEventTimeline(data) {
            const events = data.events || [];
            const timeline = document.getElementById('event-timeline');
            
            // Filter to current task events
            const taskEvents = [];
            let inCurrentTask = false;
            
            for (let i = events.length - 1; i >= 0 && taskEvents.length < 20; i--) {
                const e = events[i];
                if (e.type === 'task_start') {
                    if (inCurrentTask) break;
                    inCurrentTask = true;
                }
                if (inCurrentTask && e.type !== 'task_start') {
                    taskEvents.unshift(e);
                }
            }
            
            let html = '';
            taskEvents.forEach(e => {
                let cls = '';
                let content = '';
                
                switch(e.type) {
                    case 'defect_improvement':
                        cls = 'defect-improvement';
                        const delta = (e.before - e.after).toFixed(4);
                        content = `<span class="event-op">${e.op}</span><br>
                                   <span class="event-value">${e.before.toFixed(4)}</span> → 
                                   <span class="event-value">${e.after.toFixed(4)}</span>
                                   <span class="event-delta">(−${delta})</span>`;
                        break;
                    case 'predicate_discovery':
                        cls = 'predicate-discovery';
                        content = `🔬 <span class="event-op">${e.count} predicates</span><br>
                                   via ${e.method}`;
                        break;
                    case 'synthesis':
                        cls = 'synthesis';
                        content = `🔧 <span class="event-op">${e.program.substring(0, 40)}</span><br>
                                   defect: <span class="event-value">${e.defect.toFixed(4)}</span>`;
                        break;
                    case 'sheaf_reject':
                        cls = 'sheaf-reject';
                        content = `✗ Sheaf energy: <span class="event-value">${e.energy.toFixed(3)}</span> (rejected)`;
                        break;
                }
                
                if (content) {
                    html += `<div class="event ${cls}">${content}</div>`;
                }
            });
            
            timeline.innerHTML = html || '<div style="color:#666;padding:20px;">No events yet...</div>';
        }
        
        function updateCurrentTask(data) {
            const events = data.events || [];
            const taskStarts = events.filter(e => e.type === 'task_start');
            const lastStart = taskStarts[taskStarts.length - 1];
            
            if (lastStart) {
                document.getElementById('current-task-id').textContent = 
                    `Task: ${lastStart.task?.task_id}`;
                document.getElementById('current-task-progress').textContent = 
                    `${lastStart.task?.idx} of ${lastStart.task?.total}`;
            }
            
            // Find best defect for current task
            let bestDefect = 1.0;
            let bestIG = 0;
            let predCount = 0;
            
            let inCurrentTask = false;
            for (let i = events.length - 1; i >= 0; i--) {
                const e = events[i];
                if (e.type === 'task_start') {
                    if (inCurrentTask) break;
                    inCurrentTask = true;
                }
                if (inCurrentTask) {
                    if (e.type === 'defect_improvement') {
                        bestDefect = Math.min(bestDefect, e.after);
                        bestIG = Math.max(bestIG, e.ig);
                    }
                    if (e.type === 'predicate_discovery') {
                        predCount += e.count;
                    }
                }
            }
            
            // Update defect meter
            const fill = document.getElementById('defect-fill');
            const label = document.getElementById('defect-label');
            fill.style.width = `${bestDefect * 100}%`;
            label.textContent = `Defect: ${bestDefect.toFixed(4)}`;
            
            // Update mini stats
            document.getElementById('s-ig').textContent = bestIG.toFixed(3);
            document.getElementById('s-preds').textContent = predCount;
            
            // Track defect history
            defectHistory.push(bestDefect);
            if (defectHistory.length > 50) defectHistory.shift();
            
            igHistory.push(bestIG);
            if (igHistory.length > 50) igHistory.shift();
        }
        
        function updateCharts(data) {
            const events = data.events || [];
            
            // Defect over time chart
            Plotly.newPlot('defect-chart', [{
                y: defectHistory,
                type: 'scatter',
                mode: 'lines',
                fill: 'tozeroy',
                line: { color: '#00d4ff', width: 2 },
                fillcolor: 'rgba(0,212,255,0.2)'
            }], {
                paper_bgcolor: 'transparent',
                plot_bgcolor: 'transparent',
                margin: { t: 5, r: 5, b: 20, l: 30 },
                xaxis: { showgrid: false, showticklabels: false },
                yaxis: { range: [0, 1], gridcolor: 'rgba(255,255,255,0.1)', tickfont: { size: 9, color: '#666' } }
            }, { responsive: true, displayModeBar: false });
            
            // IG histogram
            const igData = events.filter(e => e.type === 'defect_improvement').map(e => e.ig);
            if (igData.length > 0) {
                Plotly.newPlot('ig-chart', [{
                    x: igData.slice(-100),
                    type: 'histogram',
                    marker: { color: '#00ff64' },
                    nbinsx: 20
                }], {
                    paper_bgcolor: 'transparent',
                    plot_bgcolor: 'transparent',
                    margin: { t: 10, r: 10, b: 30, l: 40 },
                    xaxis: { title: 'Information Gain', titlefont: { size: 10 }, gridcolor: 'rgba(255,255,255,0.1)' },
                    yaxis: { title: 'Count', titlefont: { size: 10 }, gridcolor: 'rgba(255,255,255,0.1)' },
                    font: { color: '#666', size: 9 }
                }, { responsive: true, displayModeBar: false });
            }
        }
        
        function escapeHtml(text) {
            const div = document.createElement('div');
            div.textContent = text;
            return div.innerHTML;
        }
        
        // Initial load
        updateDashboard();
        
        // Auto-refresh every 2 seconds
        setInterval(updateDashboard, 2000);
    </script>
</body>
</html>
'''


@app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE)


@app.route('/api/data')
def api_data():
    atlas = load_atlas()
    progress = load_progress()
    events = parse_console_output()
    
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
        'timestamp': time.time(),
    })


if __name__ == '__main__':
    # Ensure log directory exists
    ATLAS_DIR.mkdir(parents=True, exist_ok=True)
    
    print("=" * 60)
    print("  SHEAF ATLAS DASHBOARD v2 — Model Thinking Visualizer")
    print("=" * 60)
    print()
    print("  Open your browser to: http://localhost:5050")
    print()
    print("  Features:")
    print("    • Live log stream from evaluation")
    print("    • Per-puzzle defect reduction timeline")
    print("    • Task progress grid (green=perfect, red=fail)")
    print("    • Information gain histogram")
    print("    • Real-time event timeline")
    print()
    print("  Auto-refreshes every 2 seconds")
    print("  Press Ctrl+C to stop")
    print("=" * 60)
    
    app.run(host='0.0.0.0', port=5050, debug=False, threaded=True)
