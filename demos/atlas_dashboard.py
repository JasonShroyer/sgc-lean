"""
Sheaf Atlas Web Dashboard

Real-time web-based visualization of the Sheaf Atlas learning process.
Uses Flask + Plotly for interactive charts.

Features:
- Learning curve with iteration history
- Atlas growth (predicates, charts)
- Interactive manifold graph (D3.js force-directed)
- Gauge transfer distribution
- Live auto-refresh

Usage:
  python atlas_dashboard.py
  
Then open http://localhost:5050 in your browser.
"""

import os
import json
import time
from pathlib import Path
from collections import defaultdict
from flask import Flask, render_template_string, jsonify

app = Flask(__name__)

ATLAS_DIR = Path(__file__).parent.parent / "data" / "atlas"
ATLAS_FILE = ATLAS_DIR / "sheaf_atlas.json"
PROGRESS_FILE = ATLAS_DIR / "iteration_progress.json"


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


HTML_TEMPLATE = '''
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Sheaf Atlas Dashboard</title>
    <script src="https://cdn.plot.ly/plotly-2.27.0.min.js"></script>
    <script src="https://d3js.org/d3.v7.min.js"></script>
    <style>
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body {
            font-family: 'Segoe UI', system-ui, sans-serif;
            background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%);
            color: #e0e0e0;
            min-height: 100vh;
        }
        .header {
            background: rgba(0,0,0,0.3);
            padding: 20px;
            text-align: center;
            border-bottom: 2px solid #00d4ff;
        }
        .header h1 {
            font-size: 28px;
            color: #00d4ff;
            text-shadow: 0 0 20px rgba(0,212,255,0.5);
        }
        .header p {
            color: #888;
            margin-top: 5px;
        }
        .dashboard {
            display: grid;
            grid-template-columns: 1fr 1fr;
            gap: 20px;
            padding: 20px;
            max-width: 1600px;
            margin: 0 auto;
        }
        .panel {
            background: rgba(255,255,255,0.05);
            border-radius: 12px;
            padding: 20px;
            border: 1px solid rgba(255,255,255,0.1);
            backdrop-filter: blur(10px);
        }
        .panel h2 {
            font-size: 16px;
            color: #00d4ff;
            margin-bottom: 15px;
            padding-bottom: 10px;
            border-bottom: 1px solid rgba(0,212,255,0.3);
        }
        .stats-grid {
            display: grid;
            grid-template-columns: repeat(3, 1fr);
            gap: 15px;
            margin-bottom: 20px;
        }
        .stat-card {
            background: rgba(0,212,255,0.1);
            border-radius: 8px;
            padding: 15px;
            text-align: center;
        }
        .stat-value {
            font-size: 32px;
            font-weight: bold;
            color: #00d4ff;
        }
        .stat-label {
            font-size: 12px;
            color: #888;
            margin-top: 5px;
        }
        .chart-container {
            height: 300px;
        }
        .graph-container {
            height: 400px;
            background: rgba(0,0,0,0.2);
            border-radius: 8px;
            overflow: hidden;
        }
        .full-width {
            grid-column: 1 / -1;
        }
        .gauge-indicator {
            display: flex;
            align-items: center;
            gap: 20px;
            margin-top: 15px;
        }
        .gauge-bar {
            flex: 1;
            height: 30px;
            background: #333;
            border-radius: 15px;
            overflow: hidden;
            position: relative;
        }
        .gauge-fill {
            height: 100%;
            background: linear-gradient(90deg, #666 0%, #ff6b6b 100%);
            transition: width 0.5s ease;
        }
        .gauge-label {
            position: absolute;
            width: 100%;
            text-align: center;
            line-height: 30px;
            font-weight: bold;
            color: white;
            text-shadow: 1px 1px 2px black;
        }
        .holonomy-badge {
            background: #ff6b6b;
            color: white;
            padding: 5px 15px;
            border-radius: 20px;
            font-weight: bold;
            animation: pulse 2s infinite;
        }
        @keyframes pulse {
            0%, 100% { box-shadow: 0 0 0 0 rgba(255,107,107,0.7); }
            50% { box-shadow: 0 0 0 10px rgba(255,107,107,0); }
        }
        .transition-list {
            max-height: 200px;
            overflow-y: auto;
            font-family: monospace;
            font-size: 12px;
        }
        .transition-item {
            padding: 5px 10px;
            border-bottom: 1px solid rgba(255,255,255,0.1);
        }
        .transition-item.gauge { color: #ff6b6b; }
        .transition-item.identity { color: #888; }
        #manifold-graph { width: 100%; height: 100%; }
        .node { cursor: pointer; }
        .node circle { stroke: #00d4ff; stroke-width: 2px; }
        .link { stroke-opacity: 0.6; }
        .link.gauge { stroke: #ff6b6b; stroke-width: 3px; }
        .link.identity { stroke: #666; stroke-width: 1px; }
        .refresh-indicator {
            position: fixed;
            top: 10px;
            right: 10px;
            background: rgba(0,212,255,0.2);
            padding: 8px 15px;
            border-radius: 20px;
            font-size: 12px;
        }
    </style>
</head>
<body>
    <div class="header">
        <h1>🌐 Sheaf Atlas Dashboard</h1>
        <p>Real-Time Learning on the Semantic Manifold</p>
    </div>
    
    <div class="refresh-indicator" id="refresh-indicator">
        ⟳ Auto-refresh: <span id="countdown">5</span>s
    </div>
    
    <div class="dashboard">
        <!-- Stats Overview -->
        <div class="panel full-width">
            <h2>📊 Overview</h2>
            <div class="stats-grid">
                <div class="stat-card">
                    <div class="stat-value" id="stat-iteration">-</div>
                    <div class="stat-label">Current Iteration</div>
                </div>
                <div class="stat-card">
                    <div class="stat-value" id="stat-perfect">-</div>
                    <div class="stat-label">Perfect Solves</div>
                </div>
                <div class="stat-card">
                    <div class="stat-value" id="stat-best">-</div>
                    <div class="stat-label">Best Ever</div>
                </div>
                <div class="stat-card">
                    <div class="stat-value" id="stat-predicates">-</div>
                    <div class="stat-label">Atlas Predicates</div>
                </div>
                <div class="stat-card">
                    <div class="stat-value" id="stat-charts">-</div>
                    <div class="stat-label">Charts</div>
                </div>
                <div class="stat-card">
                    <div class="stat-value" id="stat-transfers">-</div>
                    <div class="stat-label">Gauge Transfers</div>
                </div>
            </div>
        </div>
        
        <!-- Learning Curve -->
        <div class="panel">
            <h2>📈 Learning Curve</h2>
            <div class="chart-container" id="learning-chart"></div>
        </div>
        
        <!-- Atlas Growth -->
        <div class="panel">
            <h2>🧠 Atlas Growth</h2>
            <div class="chart-container" id="growth-chart"></div>
        </div>
        
        <!-- Manifold Graph -->
        <div class="panel full-width">
            <h2>🌌 Manifold Structure</h2>
            <div class="graph-container" id="manifold-graph"></div>
        </div>
        
        <!-- Gauge Distribution -->
        <div class="panel">
            <h2>⚡ Gauge Transport</h2>
            <div class="gauge-indicator">
                <span>Identity</span>
                <div class="gauge-bar">
                    <div class="gauge-fill" id="gauge-fill" style="width: 0%"></div>
                    <div class="gauge-label" id="gauge-label">-</div>
                </div>
                <span>Holonomy</span>
            </div>
            <div style="margin-top: 15px; text-align: center;">
                <span class="holonomy-badge" id="holonomy-badge" style="display: none;">
                    🔄 Non-trivial Holonomy Detected!
                </span>
            </div>
        </div>
        
        <!-- Recent Transitions -->
        <div class="panel">
            <h2>🔗 Recent Transitions</h2>
            <div class="transition-list" id="transition-list">
                <div class="transition-item">No transitions yet...</div>
            </div>
        </div>
    </div>
    
    <script>
        let countdown = 5;
        
        function updateDashboard() {
            fetch('/api/data')
                .then(r => r.json())
                .then(data => {
                    updateStats(data);
                    updateLearningChart(data);
                    updateGrowthChart(data);
                    updateManifoldGraph(data);
                    updateGaugeIndicator(data);
                    updateTransitionList(data);
                })
                .catch(console.error);
        }
        
        function updateStats(data) {
            const p = data.progress || {};
            const a = data.atlas || {};
            const current = p.iterations?.[p.iterations.length - 1] || {};
            
            document.getElementById('stat-iteration').textContent = current.iteration || 0;
            document.getElementById('stat-perfect').textContent = current.perfect || 0;
            document.getElementById('stat-best').textContent = p.best_perfect || 0;
            document.getElementById('stat-predicates').textContent = a.total_predicates || 0;
            document.getElementById('stat-charts').textContent = a.num_charts || 0;
            document.getElementById('stat-transfers').textContent = 
                (a.stats?.gauge_transfers || 0);
        }
        
        function updateLearningChart(data) {
            const iterations = data.progress?.iterations || [];
            const x = iterations.map(it => it.iteration);
            const y = iterations.map(it => it.perfect);
            
            Plotly.newPlot('learning-chart', [{
                x: x, y: y,
                type: 'scatter',
                mode: 'lines+markers',
                fill: 'tozeroy',
                line: { color: '#00d4ff', width: 3 },
                marker: { size: 10, color: '#00d4ff' },
                fillcolor: 'rgba(0,212,255,0.2)'
            }], {
                paper_bgcolor: 'transparent',
                plot_bgcolor: 'transparent',
                font: { color: '#e0e0e0' },
                margin: { t: 10, r: 10, b: 40, l: 40 },
                xaxis: { title: 'Iteration', gridcolor: 'rgba(255,255,255,0.1)' },
                yaxis: { title: 'Perfect Solves', gridcolor: 'rgba(255,255,255,0.1)' }
            }, { responsive: true });
        }
        
        function updateGrowthChart(data) {
            const iterations = data.progress?.iterations || [];
            const x = iterations.map(it => it.iteration);
            const yPreds = iterations.map(it => it.atlas_size || 0);
            const yCharts = iterations.map(it => it.num_charts || 0);
            
            Plotly.newPlot('growth-chart', [
                { x: x, y: yPreds, name: 'Predicates', type: 'bar', marker: { color: '#00d4ff' } },
                { x: x, y: yCharts, name: 'Charts', type: 'bar', marker: { color: '#ff6b6b' } }
            ], {
                paper_bgcolor: 'transparent',
                plot_bgcolor: 'transparent',
                font: { color: '#e0e0e0' },
                margin: { t: 10, r: 10, b: 40, l: 40 },
                barmode: 'group',
                xaxis: { title: 'Iteration', gridcolor: 'rgba(255,255,255,0.1)' },
                yaxis: { title: 'Count', gridcolor: 'rgba(255,255,255,0.1)' },
                legend: { x: 0, y: 1 }
            }, { responsive: true });
        }
        
        function updateManifoldGraph(data) {
            const container = document.getElementById('manifold-graph');
            container.innerHTML = '';
            
            const charts = data.atlas?.charts || {};
            const transitions = data.atlas?.transitions || [];
            
            if (Object.keys(charts).length === 0) {
                container.innerHTML = '<div style="text-align:center;padding:50px;color:#666;">No manifold data yet. Charts will appear as predicates are discovered.</div>';
                return;
            }
            
            // Build graph data
            const nodes = Object.entries(charts).map(([id, c], i) => ({
                id: id.substring(0, 25),
                size: (c.sections ? Object.keys(c.sections).length : 0) * 5 + 20,
                tasks: c.task_ids?.length || 0
            }));
            
            const links = [];
            const seen = new Set();
            transitions.forEach(t => {
                const key = t.source_task_id + '-' + t.target_task_id;
                if (!seen.has(key)) {
                    seen.add(key);
                    links.push({
                        source: t.source_task_id?.substring(0, 8) || '',
                        target: t.target_task_id?.substring(0, 8) || '',
                        gauge: t.gauge_element !== 'e'
                    });
                }
            });
            
            const width = container.clientWidth;
            const height = container.clientHeight;
            
            const svg = d3.select('#manifold-graph')
                .append('svg')
                .attr('width', width)
                .attr('height', height);
            
            const simulation = d3.forceSimulation(nodes)
                .force('link', d3.forceLink(links).id(d => d.id).distance(100))
                .force('charge', d3.forceManyBody().strength(-200))
                .force('center', d3.forceCenter(width / 2, height / 2));
            
            const link = svg.append('g')
                .selectAll('line')
                .data(links)
                .enter().append('line')
                .attr('class', d => 'link ' + (d.gauge ? 'gauge' : 'identity'));
            
            const node = svg.append('g')
                .selectAll('g')
                .data(nodes)
                .enter().append('g')
                .attr('class', 'node');
            
            node.append('circle')
                .attr('r', d => d.size)
                .attr('fill', 'rgba(0,212,255,0.3)');
            
            node.append('text')
                .text(d => d.id.substring(0, 10))
                .attr('text-anchor', 'middle')
                .attr('dy', 4)
                .attr('fill', '#e0e0e0')
                .attr('font-size', '10px');
            
            simulation.on('tick', () => {
                link
                    .attr('x1', d => d.source.x)
                    .attr('y1', d => d.source.y)
                    .attr('x2', d => d.target.x)
                    .attr('y2', d => d.target.y);
                node.attr('transform', d => `translate(${d.x},${d.y})`);
            });
        }
        
        function updateGaugeIndicator(data) {
            const stats = data.atlas?.stats || {};
            const identity = stats.identity_transfers || 0;
            const gauge = stats.gauge_transfers || 0;
            const total = identity + gauge;
            
            const pct = total > 0 ? (gauge / total * 100) : 0;
            document.getElementById('gauge-fill').style.width = pct + '%';
            document.getElementById('gauge-label').textContent = 
                total > 0 ? `${gauge}/${total} (${pct.toFixed(1)}% holonomy)` : 'No transfers yet';
            
            document.getElementById('holonomy-badge').style.display = 
                gauge > 0 ? 'inline-block' : 'none';
        }
        
        function updateTransitionList(data) {
            const transitions = data.atlas?.transitions || [];
            const list = document.getElementById('transition-list');
            
            if (transitions.length === 0) {
                list.innerHTML = '<div class="transition-item">No transitions yet...</div>';
                return;
            }
            
            list.innerHTML = transitions.slice(-10).reverse().map(t => {
                const isGauge = t.gauge_element !== 'e';
                return `<div class="transition-item ${isGauge ? 'gauge' : 'identity'}">
                    ${t.predicate_name?.substring(0, 20) || '?'}: 
                    ${t.source_task_id?.substring(0, 8) || '?'} → 
                    ${t.target_task_id?.substring(0, 8) || '?'} 
                    via <strong>${t.gauge_element}</strong>
                </div>`;
            }).join('');
        }
        
        // Initial load
        updateDashboard();
        
        // Auto-refresh
        setInterval(() => {
            countdown--;
            document.getElementById('countdown').textContent = countdown;
            if (countdown <= 0) {
                countdown = 5;
                updateDashboard();
            }
        }, 1000);
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
    
    # Process atlas data
    atlas_summary = {}
    if atlas:
        charts = atlas.get('charts', {})
        atlas_summary = {
            'total_predicates': sum(len(c.get('sections', {})) for c in charts.values()),
            'num_charts': len(charts),
            'charts': charts,
            'transitions': atlas.get('transitions', [])[-50:],  # Last 50
            'stats': atlas.get('statistics', {}),
        }
    
    return jsonify({
        'atlas': atlas_summary,
        'progress': progress,
        'timestamp': time.time(),
    })


if __name__ == '__main__':
    print("=" * 60)
    print("  SHEAF ATLAS WEB DASHBOARD")
    print("=" * 60)
    print()
    print("  Open your browser to: http://localhost:5050")
    print()
    print("  The dashboard will auto-refresh every 5 seconds")
    print("  Press Ctrl+C to stop the server")
    print("=" * 60)
    
    app.run(host='0.0.0.0', port=5050, debug=False)
