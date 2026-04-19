// ═══════════════════════════════════════════════════
// StackFlow — PDA Simulator  (Vanilla JS, single file)
// ═══════════════════════════════════════════════════

// ─── PDA Engine ──────────────────────────────────
class PDAEngine {
  constructor(def) {
    this.states = def.states;
    this.inputAlphabet = def.inputAlphabet;
    this.stackAlphabet = def.stackAlphabet;
    this.transitions = def.transitions;
    this.startState = def.startState;
    this.startSymbol = def.startSymbol;
    this.acceptStates = def.acceptStates || [];
    this.acceptanceMode = def.acceptanceMode || 'finalState';
  }

  initialize(input) {
    return {
      input: [...input],
      treeNodes: [{
        id: 0, parentId: null, state: this.startState,
        inputIndex: 0, stack: [this.startSymbol],
        status: 'active', transition: null, depth: 0, epsilonCount: 0
      }],
      activeIds: [0], nextId: 1, stepCount: 0, result: null, history: []
    };
  }

  step(sim) {
    if (sim.result) return sim;
    const history = [...sim.history, { activeIds: [...sim.activeIds], len: sim.treeNodes.length }];
    const nodes = [...sim.treeNodes];
    const newActive = [];
    let nextId = sim.nextId;

    for (const aid of sim.activeIds) {
      const node = nodes[aid];
      if (node.status !== 'active') continue;
      const matches = this._findTrans(node, sim.input);
      if (matches.length === 0) {
        nodes[aid] = { ...node, status: this._check(node, sim.input) ? 'accepted' : 'dead' };
        continue;
      }
      nodes[aid] = { ...node, status: 'processed' };
      for (const t of matches) {
        const ns = [...node.stack];
        // Safer pop logic: explicitly match top, or handle epsilon pop
        if (t.popSymbol !== 'ε') {
          if (ns.length === 0 || ns[ns.length - 1] !== t.popSymbol) continue; // Safety check
          ns.pop();
        }

        const ps = t.pushSymbols.filter(s => s !== 'ε' && s !== '');
        for (let i = ps.length - 1; i >= 0; i--) ns.push(ps[i]);

        const ni = t.inputSymbol === 'ε' ? node.inputIndex : node.inputIndex + 1;
        const ec = t.inputSymbol === 'ε' ? node.epsilonCount + 1 : 0;

        // Prevent infinite epsilon loops with hardcap (safeguard)
        if (ec > 100) {
          console.warn('Infinite ε-loop detected and halted');
          continue;
        }

        const child = {
          id: nextId++, parentId: node.id, state: t.toState, inputIndex: ni,
          stack: ns, status: 'active', transition: t, depth: node.depth + 1, epsilonCount: ec
        };
        if (this._check(child, sim.input)) child.status = 'accepted';
        nodes.push(child);
        if (nodes.length > 5000) {
          console.warn('Too many configurations, stopping');
          return { ...sim, treeNodes: nodes, activeIds: [], nextId, stepCount: sim.stepCount + 1, result: 'rejected', history };
        }
        if (child.status === 'active') newActive.push(child.id);
      }
    }
    let result = null;
    if (nodes.some(n => n.status === 'accepted')) result = 'accepted';
    else if (newActive.length === 0) result = 'rejected';

    return { ...sim, treeNodes: nodes, activeIds: newActive, nextId, stepCount: sim.stepCount + 1, result, history };
  }

  stepBack(sim) {
    if (!sim.history.length) return sim;
    const prev = sim.history[sim.history.length - 1];
    const restored = sim.treeNodes.slice(0, prev.len).map((n, i) =>
      prev.activeIds.includes(i) ? { ...n, status: 'active' } : n);
    return {
      ...sim, treeNodes: restored, activeIds: prev.activeIds, nextId: prev.len,
      stepCount: Math.max(0, sim.stepCount - 1), result: null, history: sim.history.slice(0, -1)
    };
  }

  _findTrans(node, input) {
    const top = node.stack.length ? node.stack[node.stack.length - 1] : null;
    const inp = node.inputIndex < input.length ? input[node.inputIndex] : null;
    return this.transitions.filter(t =>
      t.fromState === node.state &&
      (t.popSymbol === top) &&
      (t.inputSymbol === 'ε' || t.inputSymbol === inp));
  }

  _check(node, input) {
    if (node.inputIndex < input.length) return false;
    if (this.acceptanceMode === 'finalState') return this.acceptStates.includes(node.state);
    if (this.acceptanceMode === 'emptyStack') return node.stack.length === 0;
    return this.acceptStates.includes(node.state) || node.stack.length === 0;
  }
}

// ─── CFG → PDA ─────────────────────────────────
function parseCFG(text) {
  const lines = text.split('\n').map(l => l.trim()).filter(l => l);
  const vars = new Set(), terms = new Set(), rules = [];
  let startVar = null;
  for (const line of lines) {
    const parts = line.split('->');
    if (parts.length !== 2) throw new Error(`Invalid format in rule: '${line}'. Missing or multiple '->'`);
    const [lhs, rhs] = parts.map(s => s.trim());
    if (!lhs) throw new Error(`Missing left-hand side in rule: '${line}'`);
    if (!rhs) throw new Error(`Missing right-hand side in rule: '${line}'`);
    vars.add(lhs); if (!startVar) startVar = lhs;
    for (const alt of rhs.split('|').map(s => s.trim())) {
      if (alt === 'ε' || alt === '') { rules.push({ lhs: lhs.trim(), rhs: [] }); continue; }
      const syms = [];
      for (const ch of alt) {
        if (ch === ' ') continue; syms.push(ch);
        if (ch >= 'A' && ch <= 'Z') vars.add(ch); else terms.add(ch);
      }
      rules.push({ lhs: lhs.trim(), rhs: syms });
    }
  }
  return { variables: [...vars], terminals: [...terms], rules, startVariable: startVar };
}

function cfgToPDA(cfg) {
  const trans = [];
  trans.push({ fromState: 'q_start', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q_loop', pushSymbols: [cfg.startVariable, 'Z'] });
  for (const r of cfg.rules)
    trans.push({ fromState: 'q_loop', inputSymbol: 'ε', popSymbol: r.lhs, toState: 'q_loop', pushSymbols: r.rhs.length ? [...r.rhs] : [] });
  for (const t of cfg.terminals)
    trans.push({ fromState: 'q_loop', inputSymbol: t, popSymbol: t, toState: 'q_loop', pushSymbols: [] });
  trans.push({ fromState: 'q_loop', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q_accept', pushSymbols: ['Z'] });
  return {
    states: ['q_start', 'q_loop', 'q_accept'], inputAlphabet: [...cfg.terminals],
    stackAlphabet: [...new Set(['Z', ...cfg.variables, ...cfg.terminals])],
    startState: 'q_start', startSymbol: 'Z', acceptStates: ['q_accept'], transitions: trans
  };
}

// ─── Examples ────────────────────────────────────
const PDA_EXAMPLES = [
  {
    id: 'anbn', name: 'aⁿbⁿ', language: 'a^n b^n', description: 'Equal a\'s followed by b\'s', acceptanceMode: 'finalState',
    testStrings: { accept: ['', 'ab', 'aabb', 'aaabbb'], reject: ['a', 'b', 'aab', 'abb', 'ba'] },
    definition: {
      states: ['q0', 'q1', 'q2'], inputAlphabet: ['a', 'b'], stackAlphabet: ['Z', 'A'],
      startState: 'q0', startSymbol: 'Z', acceptStates: ['q2'], transitions: [
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'Z', toState: 'q0', pushSymbols: ['A', 'Z'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'A', toState: 'q0', pushSymbols: ['A', 'A'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'A', toState: 'q1', pushSymbols: [] },
        { fromState: 'q1', inputSymbol: 'b', popSymbol: 'A', toState: 'q1', pushSymbols: [] },
        { fromState: 'q1', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] }]
    }
  },
  {
    id: 'parens', name: 'Balanced Parentheses', language: 'Balanced Parentheses', description: 'Nested parentheses', acceptanceMode: 'finalState',
    testStrings: { accept: ['', '()', '(())', '()()', '((()))'], reject: ['(', ')', ')(', '))('] },
    definition: {
      states: ['q0', 'qf'], inputAlphabet: ['(', ')'], stackAlphabet: ['Z', 'X'],
      startState: 'q0', startSymbol: 'Z', acceptStates: ['qf'], transitions: [
        { fromState: 'q0', inputSymbol: '(', popSymbol: 'Z', toState: 'q0', pushSymbols: ['X', 'Z'] },
        { fromState: 'q0', inputSymbol: '(', popSymbol: 'X', toState: 'q0', pushSymbols: ['X', 'X'] },
        { fromState: 'q0', inputSymbol: ')', popSymbol: 'X', toState: 'q0', pushSymbols: [] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'Z', toState: 'qf', pushSymbols: ['Z'] }]
    }
  },
  {
    id: 'palindrome', name: 'Even Palindromes (wwᴿ)', language: 'Even Palindromes (wwᴿ)', description: 'Even-length palindromes over {a,b}', acceptanceMode: 'finalState',
    testStrings: { accept: ['', 'aa', 'bb', 'abba', 'baab'], reject: ['a', 'ab', 'aba', 'aab'] },
    definition: {
      states: ['q0', 'q1', 'q2'], inputAlphabet: ['a', 'b'], stackAlphabet: ['Z', 'a', 'b'],
      startState: 'q0', startSymbol: 'Z', acceptStates: ['q2'], transitions: [
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'Z', toState: 'q0', pushSymbols: ['a', 'Z'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'Z', toState: 'q0', pushSymbols: ['b', 'Z'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'a', toState: 'q0', pushSymbols: ['a', 'a'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'b', toState: 'q0', pushSymbols: ['a', 'b'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'a', toState: 'q0', pushSymbols: ['b', 'a'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'b', toState: 'q0', pushSymbols: ['b', 'b'] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q1', pushSymbols: ['Z'] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'a', toState: 'q1', pushSymbols: ['a'] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'b', toState: 'q1', pushSymbols: ['b'] },
        { fromState: 'q1', inputSymbol: 'a', popSymbol: 'a', toState: 'q1', pushSymbols: [] },
        { fromState: 'q1', inputSymbol: 'b', popSymbol: 'b', toState: 'q1', pushSymbols: [] },
        { fromState: 'q1', inputSymbol: 'ε', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] }]
    }
  },
  {
    id: 'equal-ab', name: 'Equal a\'s and b\'s', language: 'Equal a\'s and b\'s', description: '#a = #b in any order', acceptanceMode: 'finalState',
    testStrings: { accept: ['', 'ab', 'ba', 'aabb', 'abab', 'bbaa'], reject: ['a', 'b', 'aab', 'bba'] },
    definition: {
      states: ['q0', 'qf'], inputAlphabet: ['a', 'b'], stackAlphabet: ['Z', 'A', 'B'],
      startState: 'q0', startSymbol: 'Z', acceptStates: ['qf'], transitions: [
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'Z', toState: 'q0', pushSymbols: ['A', 'Z'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'A', toState: 'q0', pushSymbols: ['A', 'A'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'B', toState: 'q0', pushSymbols: [] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'Z', toState: 'q0', pushSymbols: ['B', 'Z'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'B', toState: 'q0', pushSymbols: ['B', 'B'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'A', toState: 'q0', pushSymbols: [] },
        { fromState: 'q0', inputSymbol: 'ε', popSymbol: 'Z', toState: 'qf', pushSymbols: ['Z'] }]
    }
  },
  {
    id: 'more-bs', name: 'aⁱbʲ (i < j)', language: 'a^i b^j (i < j)', description: 'More b\'s than a\'s', acceptanceMode: 'finalState',
    testStrings: { accept: ['b', 'abb', 'aabbb', 'bb'], reject: ['', 'a', 'ab', 'aabb', 'ba'] },
    definition: {
      states: ['q0', 'q1', 'q2'], inputAlphabet: ['a', 'b'], stackAlphabet: ['Z', 'A'],
      startState: 'q0', startSymbol: 'Z', acceptStates: ['q2'], transitions: [
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'Z', toState: 'q0', pushSymbols: ['A', 'Z'] },
        { fromState: 'q0', inputSymbol: 'a', popSymbol: 'A', toState: 'q0', pushSymbols: ['A', 'A'] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'A', toState: 'q1', pushSymbols: [] },
        { fromState: 'q0', inputSymbol: 'b', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] },
        { fromState: 'q1', inputSymbol: 'b', popSymbol: 'A', toState: 'q1', pushSymbols: [] },
        { fromState: 'q1', inputSymbol: 'b', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] },
        { fromState: 'q2', inputSymbol: 'b', popSymbol: 'Z', toState: 'q2', pushSymbols: ['Z'] }]
    }
  }
];

const CFG_EXAMPLES = [
  { id: 'cfg-anbn', name: 'S → aSb | ε', language: 'S → aSb | ε', grammar: 'S -> aSb | ε', testStrings: { accept: ['', 'ab', 'aabb'], reject: ['a', 'ba'] } },
  { id: 'cfg-parens', name: 'S → (S) | SS | ε', language: 'S → (S) | SS | ε', grammar: 'S -> (S) | SS | ε', testStrings: { accept: ['', '()', '(())'], reject: ['(', ')'] } },
  { id: 'cfg-palindrome', name: 'S → aSa | bSb | ε', language: 'S → aSa | bSb | ε', grammar: 'S -> aSa | bSb | ε', testStrings: { accept: ['', 'aa', 'abba'], reject: ['a', 'ab'] } },
];

// ─── App State ───────────────────────────────────
let currentLanguage = '';
let pdaDef = null, engine = null, simState = null, inputString = '';
let acceptanceMode = 'finalState', isPlaying = false, speed = 500, playTimer = null, activeExId = null;
let exTab = 'pda';

const $ = id => document.getElementById(id);

// ─── Initialize ──────────────────────────────────
function init() {
  renderExampleTabs();
  renderExamples();
  $('speed-slider').addEventListener('input', updateSpeed);
  // Load first example automatically
  loadExample(PDA_EXAMPLES[0]);
}

// ─── Examples ────────────────────────────────────
function renderExampleTabs() {
  $('example-tabs').innerHTML =
    `<button class="btn ${exTab === 'pda' ? 'btn-primary' : ''}" onclick="switchTab('pda')" style="font-size:.72rem;padding:4px 12px">PDA Examples</button>` +
    `<button class="btn ${exTab === 'cfg' ? 'btn-primary' : ''}" onclick="switchTab('cfg')" style="font-size:.72rem;padding:4px 12px">CFG → PDA</button>`;
}

function switchTab(tab) { exTab = tab; renderExampleTabs(); renderExamples(); }

function renderExamples() {
  const c = $('example-cards'), t = $('test-strings');
  if (exTab === 'pda') {
    c.innerHTML = PDA_EXAMPLES.map(ex =>
      `<button class="example-card ${activeExId === ex.id ? 'active' : ''}" onclick="loadExample(PDA_EXAMPLES.find(e=>e.id==='${ex.id}'))" title="${ex.description}">${ex.name}</button>`
    ).join('');
    const active = PDA_EXAMPLES.find(e => e.id === activeExId);
    if (active) {
      t.innerHTML = '<span class="input-label" style="margin-right:4px">Test:</span>' +
        active.testStrings.accept.slice(0, 4).map(s =>
          `<button class="test-chip accept" onclick="setInput('${s}')">${s || 'ε'} ✓</button>`).join('') +
        active.testStrings.reject.slice(0, 3).map(s =>
          `<button class="test-chip reject" onclick="setInput('${s}')">${s} ✗</button>`).join('');
    } else t.innerHTML = '';
  } else {
    c.innerHTML = CFG_EXAMPLES.map(ex =>
      `<button class="example-card" onclick="loadCFGExample('${ex.id}')" title="${ex.description}">${ex.name}</button>`
    ).join('');
    t.innerHTML = '';
  }
}

function loadExample(ex) {
  currentLanguage = ex.language || ex.name;
  activeExId = ex.id;
  acceptanceMode = ex.acceptanceMode || 'finalState';
  document.querySelector(`input[name="mode"][value="${acceptanceMode}"]`).checked = true;
  pdaDef = ex.definition;
  engine = new PDAEngine({ ...pdaDef, acceptanceMode });
  simState = null; isPlaying = false; clearTimeout(playTimer);
  inputString = ex.testStrings.accept[1] || ex.testStrings.accept[0] || '';
  $('input-string').value = inputString;
  $('btn-run').disabled = false;
  renderExamples();
  renderAll();
}

function loadCFGExample(id) {
  const ex = CFG_EXAMPLES.find(e => e.id === id);
  if (!ex) return;
  try {
    const cfg = parseCFG(ex.grammar);
    pdaDef = cfgToPDA(cfg);
  } catch (e) {
    alert("CFG Parsing Error:\n" + e.message);
    return;
  }
  currentLanguage = ex.language || ex.name;
  activeExId = null; acceptanceMode = 'finalState';
  engine = new PDAEngine({ ...pdaDef, acceptanceMode });
  simState = null; isPlaying = false; clearTimeout(playTimer);
  inputString = ex.testStrings.accept[1] || ex.testStrings.accept[0] || '';
  $('input-string').value = inputString;
  $('btn-run').disabled = false;
  renderExamples(); renderAll();
}

function setInput(s) { inputString = s; $('input-string').value = s; }

function startSimulation() {
  if (!pdaDef) return false;
  const str = $('input-string').value;
  if (pdaDef.inputAlphabet && pdaDef.inputAlphabet.length) {
    for (const ch of str) {
      if (!pdaDef.inputAlphabet.includes(ch)) {
        alert("Invalid input symbol: '" + ch + "'\nAllowed: {" + pdaDef.inputAlphabet.join(', ') + "}");
        return false;
      }
    }
  }
  inputString = str;
  engine = new PDAEngine({ ...pdaDef, acceptanceMode });
  simState = engine.initialize(inputString);

  renderAll();

  // Auto-play automatically on Run
  isPlaying = true;
  updateControls();
  clearTimeout(playTimer);
  playTimer = setTimeout(autoPlay, speed);

  return true;
}

function doStepForward() {
  if (!simState && pdaDef) {
    if (!startSimulation()) return;
    return; // first step just initializes and renders
  }
  if (!simState || simState.result || !engine) return;
  simState = engine.step(simState);
  if (simState.result) isPlaying = false;
  renderAll();
}

function doStepBack() {
  if (!simState || !engine) return;
  simState = engine.stepBack(simState);
  renderAll();
}

function togglePlay() {
  if (!simState && pdaDef) {
    if (!startSimulation()) return;
    isPlaying = true; updateControls();
    playTimer = setTimeout(autoPlay, speed);
    return;
  }
  if (isPlaying) { isPlaying = false; clearTimeout(playTimer); updateControls(); }
  else { isPlaying = true; updateControls(); playTimer = setTimeout(autoPlay, speed); }
}

function autoPlay() {
  if (!isPlaying || !simState || simState.result) { isPlaying = false; updateControls(); return; }
  simState = engine.step(simState);
  if (simState.result) isPlaying = false;
  renderAll();
  if (isPlaying) playTimer = setTimeout(autoPlay, speed);
}

function resetSim() {
  if (!engine) return;
  simState = engine.initialize(inputString);
  isPlaying = false; clearTimeout(playTimer);
  renderAll();
}

function setMode(m) { acceptanceMode = m; if (pdaDef) engine = new PDAEngine({ ...pdaDef, acceptanceMode: m }); }
function updateSpeed() { speed = 1550 - parseInt($('speed-slider').value); $('speed-label').textContent = speed + 'ms'; }

// ─── Render All ──────────────────────────────────
function renderAll() {
  renderStateDiagram();
  renderStack();
  renderTape();
  renderTransitionTable();
  renderComputationTree();
  renderIDDisplay();
  renderResult();

  const langEl = document.getElementById('language-display');
  if (langEl) {
    langEl.textContent = currentLanguage ? "Language: " + currentLanguage : "Language: —";
  }
  updateControls();
  if (pdaDef) $('pda-info').textContent = `${pdaDef.states.length} states · ${pdaDef.transitions.length} rules`;
}

// ─── State Diagram ───────────────────────────────
function renderStateDiagram() {
  const el = $('state-diagram-container');
  if (!pdaDef) { el.innerHTML = '<div class="empty-state"><span class="icon">◎</span><p>Load a PDA to see the state diagram</p></div>'; return; }
  // PAD reserves space top+bottom for self-loop labels.
  const PAD = 45;
  const W = 310, H = 260;
  const R = 18;
  const n = pdaDef.states.length;
  const cx = W / 2;
  const cy = H / 2 - 10;
  const lr = Math.min(cx, cy) - PAD;
  const pos = {};
  pdaDef.states.forEach((s, i) => {
    const a = (2 * Math.PI * i) / n - Math.PI / 2;
    pos[s] = { x: cx + lr * Math.cos(a), y: cy + lr * Math.sin(a), a: a };
  });

  // Active sets
  const aStates = new Set(simState ? simState.activeIds.map(id => simState.treeNodes[id]?.state).filter(Boolean) : []);
  const aTrans = simState ? simState.activeIds.map(id => simState.treeNodes[id]?.transition).filter(Boolean) : [];
  const aTransKeys = new Set(aTrans.map(t => `${t.fromState}|${t.inputSymbol}|${t.popSymbol}|${t.toState}`));

  // Group transitions by edge
  const groups = {};
  pdaDef.transitions.forEach(t => {
    const k = t.fromState === t.toState ? `self:${t.fromState}` : `${t.fromState}->${t.toState}`;
    if (!groups[k]) groups[k] = { from: t.fromState, to: t.toState, trans: [] };
    groups[k].trans.push(t);
  });

  function fmtLabel(t) {
    const p = t.pushSymbols.filter(s => s !== 'ε' && s !== '');
    return `${t.inputSymbol}, ${t.popSymbol}/${p.length ? p.join('') : 'ε'}`;
  }

  let svg = `<svg class="state-diagram-svg" viewBox="0 0 ${W} ${H}" preserveAspectRatio="xMidYMid meet">
    <defs>
      <marker id="arr" viewBox="0 0 10 7" refX="10" refY="3.5" markerWidth="6.5" markerHeight="4.5" orient="auto-start-reverse"><polygon points="0 0,10 3.5,0 7" fill="#475569"/></marker>
      <marker id="arrA" viewBox="0 0 10 7" refX="10" refY="3.5" markerWidth="6.5" markerHeight="4.5" orient="auto-start-reverse"><polygon points="0 0,10 3.5,0 7" fill="#00f0ff"/></marker>
      <filter id="gf"><feGaussianBlur stdDeviation="4" result="b"/><feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>
    </defs>`;

  for (const [k, g] of Object.entries(groups)) {
    const anyA = g.trans.some(t => aTransKeys.has(`${t.fromState}|${t.inputSymbol}|${t.popSymbol}|${t.toState}`));
    const ac = anyA ? ' active' : '';
    const mk = anyA ? 'url(#arrA)' : 'url(#arr)';
    const label = g.trans.map(fmtLabel);

    if (g.from === g.to) {
      const p = pos[g.from]; if (!p) continue;
      const loopR = 15;
      const da = 0.55;
      const ang = p.a !== undefined ? p.a : -Math.PI / 2;
      const sx = p.x + R * Math.cos(ang - da), sy = p.y + R * Math.sin(ang - da);
      const ex = p.x + R * Math.cos(ang + da), ey = p.y + R * Math.sin(ang + da);
      svg += `<path d="M ${sx},${sy} A ${loopR},${loopR} 0 1,1 ${ex},${ey}" class="edge-path${ac}" marker-end="${mk}" fill="none"/>`;

      const dist = R + loopR * 2 + 8;
      let lx = p.x + dist * Math.cos(ang);
      let ly = p.y + dist * Math.sin(ang) + 4;

      let anchor = 'middle';
      if (Math.cos(ang) > 0.4) { anchor = 'start'; lx += 2; }
      else if (Math.cos(ang) < -0.4) { anchor = 'end'; lx -= 2; }

      const lineH = 11.5;
      const off = (label.length - 1) * lineH / 2;
      label.forEach((l, i) => {
        svg += `<text x="${lx}" y="${ly + i * lineH - off}" text-anchor="${anchor}" class="edge-label${ac}">${l}</text>`;
      });
    } else {
      const p1 = pos[g.from], p2 = pos[g.to]; if (!p1 || !p2) continue;
      const dx = p2.x - p1.x, dy = p2.y - p1.y, d = Math.sqrt(dx * dx + dy * dy);
      if (d === 0) continue;
      const ux = dx / d, uy = dy / d;
      const x1 = p1.x + ux * R, y1 = p1.y + uy * R, x2 = p2.x - ux * R, y2 = p2.y - uy * R;
      const hasRev = !!groups[`${g.to}->${g.from}`];

      let pathD, lx, ly;
      if (hasRev) {
        const co = 35;
        const mx = (x1 + x2) / 2 - uy * co, my = (y1 + y2) / 2 + ux * co;
        pathD = `M ${x1},${y1} Q ${mx},${my} ${x2},${y2}`;
        lx = (x1 + x2) / 2 - uy * (co / 2 + 14);
        ly = (y1 + y2) / 2 + ux * (co / 2 + 14);
      } else {
        pathD = `M ${x1},${y1} L ${x2},${y2}`;
        let nx = -uy, ny = ux;
        const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
        if ((mx - cx) * nx + (my - cy) * ny < 0) { nx = -nx; ny = -ny; }
        lx = mx + nx * 24;
        ly = my + ny * 24;
      }
      svg += `<path d="${pathD}" class="edge-path${ac}" marker-end="${mk}" fill="none"/>`;

      const lineH = 11.5;
      const off = (label.length - 1) * lineH / 2;
      label.forEach((l, i) => {
        svg += `<text x="${lx}" y="${ly + i * lineH - off + 4}" text-anchor="middle" class="edge-label${ac}">${l}</text>`;
      });
    }
  }

  // Draw states ON TOP of edges so circles cover any label that still clips into them
  pdaDef.states.forEach(s => {
    const p = pos[s]; if (!p) return;
    const isA = aStates.has(s), isAcc = pdaDef.acceptStates.includes(s), isStart = s === pdaDef.startState;
    const filt = isA ? ' filter="url(#gf)"' : '';
    if (isStart) svg += `<line x1="${p.x - R - 18}" y1="${p.y}" x2="${p.x - R - 2}" y2="${p.y}" stroke="#94a3b8" stroke-width="1.5" marker-end="url(#arr)"/>`;
    if (isAcc) svg += `<circle cx="${p.x}" cy="${p.y}" r="${R + 5}" fill="none" stroke="${isA ? '#00f0ff' : '#475569'}" stroke-width="1.5"${filt}/>`;
    svg += `<circle cx="${p.x}" cy="${p.y}" r="${R}" fill="${isA ? 'rgba(0,240,255,.15)' : 'rgba(13,18,37,.95)'}" stroke="${isA ? '#00f0ff' : '#475569'}" stroke-width="${isA ? 2.5 : 1.5}"${filt}/>`;
    svg += `<text x="${p.x}" y="${p.y + 4}" text-anchor="middle" font-size="11" font-weight="600" fill="${isA ? '#00f0ff' : '#e2e8f0'}">${s}</text>`;
  });

  svg += '</svg>';
  el.innerHTML = svg;
  $('active-states-badge').textContent = aStates.size ? 'Active: ' + [...aStates].join(', ') : '';
}

// ─── Stack ───────────────────────────────────────
function renderStack() {
  const el = $('stack-container');
  const stack = simState && simState.activeIds.length
    ? simState.treeNodes[simState.activeIds[0]].stack : (simState && simState.treeNodes.length ? simState.treeNodes[simState.treeNodes.length - 1].stack : []);
  const activeBranches = simState ? simState.activeIds.length : 0;
  const branchLabel = activeBranches > 1 ? ` (Displaying one active branch for visualization)` : '';
  $('stack-count').textContent = stack.length + ' items' + branchLabel;
  if (!stack.length) {
    el.innerHTML = '<div class="stack-container"><span class="stack-top-label">Stack</span><div class="stack-visual"><span class="stack-empty-msg">Empty</span></div><div class="stack-bottom-bar"></div></div>';
    return;
  }
  const rev = [...stack].reverse();
  let html = '<div class="stack-container"><span class="stack-top-label">Top ↓</span><div class="stack-visual">';
  rev.forEach((sym, vi) => {
    const cls = vi === 0 ? 'top' : (sym === 'Z' && vi === rev.length - 1 ? 'bottom-marker' : 'regular');
    html += `<div class="stack-block ${cls}">${sym}</div>`;
  });
  html += '</div><div class="stack-bottom-bar"></div></div>';
  el.innerHTML = html;
}

// ─── Tape ────────────────────────────────────────
function renderTape() {
  const el = $('tape-container');
  const input = simState ? simState.input : [...inputString];
  const primary = simState && simState.activeIds.length ? simState.treeNodes[simState.activeIds[0]] : null;
  const headIdx = primary ? primary.inputIndex : 0;
  const isActive = !!simState;

  const activeBranches = simState ? simState.activeIds.length : 0;
  const branchLabel = activeBranches > 1 ? ` (Branch 1 of ${activeBranches})` : '';

  if (!input.length && !isActive) {
    el.innerHTML = '<span class="tape-empty-msg">Enter an input string and press Run to begin</span>';
    $('tape-badge').textContent = 'Head: 0 / 0'; return;
  }
  const cells = [...input, '⊔', '⊔', '⊔'];
  let html = '<div class="tape-wrapper">';
  cells.forEach((sym, i) => {
    const isBlank = i >= input.length;
    const isCur = i === headIdx && isActive;
    const isCon = i < headIdx && !isBlank;
    let cls = 'tape-cell';
    if (isCur) cls += ' current'; else if (isCon) cls += ' consumed';
    if (isBlank) cls += ' blank';
    html += `<div class="${cls}">${sym}</div>`;
  });
  html += '</div>';
  el.innerHTML = html;
  $('tape-badge').textContent = `Head: ${headIdx} / ${input.length}` + branchLabel;
}

// ─── Transition Table ────────────────────────────
function renderTransitionTable() {
  const el = $('transition-table-container');
  if (!pdaDef || !pdaDef.transitions.length) { el.innerHTML = '<div class="empty-state"><span class="icon">δ</span><p>No transitions defined</p></div>'; return; }
  const aTrans = simState ? simState.activeIds.map(id => simState.treeNodes[id]?.transition).filter(Boolean) : [];
  const aSet = new Set(aTrans.map(t => `${t.fromState}|${t.inputSymbol}|${t.popSymbol}|${t.toState}|${t.pushSymbols.join(',')}`));

  let html = '<div class="transition-table-scroll"><table class="transition-table"><thead><tr><th>State</th><th>Input</th><th>Pop</th><th>→</th><th>State</th><th>Push</th></tr></thead><tbody>';
  pdaDef.transitions.forEach(t => {
    const key = `${t.fromState}|${t.inputSymbol}|${t.popSymbol}|${t.toState}|${t.pushSymbols.join(',')}`;
    const ac = aSet.has(key) ? ' class="active-rule"' : '';
    const ps = t.pushSymbols.filter(s => s !== 'ε' && s !== '');
    html += `<tr${ac}><td>${t.fromState}</td><td>${t.inputSymbol}</td><td>${t.popSymbol}</td><td style="color:var(--text-muted)">→</td><td>${t.toState}</td><td>${ps.length ? ps.join('') : 'ε'}</td></tr>`;
  });
  html += '</tbody></table></div>';
  el.innerHTML = html;
}

// ─── Computation Tree ────────────────────────────
function renderComputationTree() {
  const el = $('tree-container');
  if (!simState || !simState.treeNodes.length) { el.innerHTML = '<div class="empty-state"><span class="icon">🌳</span><p>Run simulation to see computation tree</p></div>'; $('tree-badge').textContent = ''; return; }

  const nodes = simState.treeNodes;
  const NR = 12, LH = 40, MW = 32;
  // Group by depth
  const levels = {};
  let maxD = 0;
  nodes.forEach(n => { if (!levels[n.depth]) levels[n.depth] = []; levels[n.depth].push(n); maxD = Math.max(maxD, n.depth); });
  const w = Math.max(200, Math.max(...Object.values(levels).map(l => l.length)) * MW + 60);
  const h = (maxD + 1) * LH + 40;
  const pos = {};
  Object.entries(levels).forEach(([d, lvl]) => {
    const sp = w / (lvl.length + 1);
    lvl.forEach((n, i) => { pos[n.id] = { x: sp * (i + 1), y: parseInt(d) * LH + 30 }; });
  });
  const aSet = new Set(simState.activeIds);

  let svg = `<div style="overflow:auto;max-height:200px"><svg class="computation-tree-svg" viewBox="0 0 ${w} ${h}" style="min-width:${w}px;min-height:${h}px">`;
  // Edges
  nodes.forEach(n => {
    if (n.parentId !== null && pos[n.parentId] && pos[n.id]) {
      svg += `<line x1="${pos[n.parentId].x}" y1="${pos[n.parentId].y}" x2="${pos[n.id].x}" y2="${pos[n.id].y}" class="tree-edge"/>`;
    }
  });
  // Nodes
  const colors = { accepted: '#00ff88', dead: '#ff4466', active: '#00f0ff', processed: '#475569' };
  const fills = { accepted: 'rgba(0,255,136,.15)', dead: 'rgba(255,68,102,.1)', active: 'rgba(0,240,255,.15)', processed: 'rgba(13,18,37,.8)' };
  nodes.forEach(n => {
    if (!pos[n.id]) return;
    const c = colors[n.status] || '#475569', f = fills[n.status] || fills.processed;
    const p = pos[n.id];
    svg += `<circle cx="${p.x}" cy="${p.y}" r="${NR}" fill="${f}" stroke="${c}" stroke-width="${aSet.has(n.id) ? 2 : 1}"/>`;
    const label = n.state.replace('q_', 'q');
    svg += `<text x="${p.x}" y="${p.y + 4}" class="tree-node" fill="${c}" text-anchor="middle" font-size="10">${label}</text>`;
    if (n.status === 'accepted') svg += `<text x="${p.x + NR + 3}" y="${p.y + 4}" font-size="10" fill="#00ff88" font-family="var(--font-mono)">✓</text>`;
    if (n.status === 'dead') svg += `<text x="${p.x + NR + 3}" y="${p.y + 4}" font-size="10" fill="#ff4466" font-family="var(--font-mono)">✗</text>`;
  });
  svg += '</svg></div>';
  el.innerHTML = svg;
  $('tree-badge').textContent = `${simState.activeIds.length} active · ${nodes.length} total`;
}

// ─── ID Display ──────────────────────────────────
function renderIDDisplay() {
  const el = $('id-display');
  if (!simState) { el.innerHTML = '<span class="badge badge-cyan">Ready</span>'; return; }
  const primary = simState.activeIds.length ? simState.treeNodes[simState.activeIds[0]]
    : simState.treeNodes[simState.treeNodes.length - 1];
  if (!primary) { el.innerHTML = `<span class="badge badge-cyan">Step ${simState.stepCount}</span>`; return; }
  const rem = simState.input.slice(primary.inputIndex).join('') || 'ε';
  const stk = primary.stack.length ? [...primary.stack].reverse().join('') : 'ε';
  let html = `<span class="badge badge-cyan">Step ${simState.stepCount}</span>`;
  html += `<span class="id-badge state-badge">State: ${primary.state}</span>`;
  html += `<span class="id-badge input-badge">Input: ${rem}</span>`;
  html += `<span class="id-badge stack-badge">Stack: ${stk}</span>`;
  if (primary.transition) {
    const t = primary.transition;
    html += `<div class="id-badge" style="background:rgba(0,240,255,0.08);border:1px solid rgba(0,240,255,0.25);color:#00f0ff">δ(${t.fromState}, ${t.inputSymbol}, ${t.popSymbol}) → (${t.toState}, ${t.pushSymbols.join('') || 'ε'})</div>`;
  }
  if (simState.activeIds.length > 1) html += `<span class="branches-label">+${simState.activeIds.length - 1} branch${simState.activeIds.length > 2 ? 'es' : ''}</span>`;
  el.innerHTML = html;
}

// ─── Result Banner ───────────────────────────────
function renderResult() {
  const el = $('result-banner');
  if (!simState || !simState.result) { el.style.display = 'none'; return; }
  el.style.display = 'flex';
  el.className = `result-banner ${simState.result}`;
  const icon = simState.result === 'accepted' ? '✓ ACCEPTED' : '✗ REJECTED';
  el.innerHTML = `${icon} <span style="font-weight:400;font-size:.75rem;opacity:.8">— ${simState.stepCount} step${simState.stepCount !== 1 ? 's' : ''} · ${simState.treeNodes.length} configs explored</span>`;
}

// ─── Controls State ──────────────────────────────
function updateControls() {
  const hasSim = !!simState, hasResult = !!(simState?.result), hasHist = !!(simState?.history?.length);
  $('btn-step-back').disabled = !hasSim || !hasHist;
  $('btn-play').disabled = !hasSim && !pdaDef;
  $('btn-play').textContent = isPlaying ? '⏸' : '▶';
  $('btn-step-forward').disabled = !hasSim || hasResult;
  $('btn-reset').disabled = !hasSim;
}

// ─── Modal ───────────────────────────────────────
function openModal(mode) {
  $('modal-overlay').style.display = 'flex';
  if (mode === 'pda') {
    $('modal-content').innerHTML = `
      <h2>Define Custom PDA</h2>
      <p class="form-hint">Transitions: one per line as <code style="color:var(--cyan);font-family:var(--font-mono);font-size:.75rem">fromState, input, pop, toState, push</code> (use ε for epsilon)</p>
      <div class="input-group">
        <label class="input-label">Language Name</label>
        <input id="custom-language" class="input" placeholder="Even a-count" />
      </div>
      <div class="form-row">
        <div class="form-group"><label>States (comma-separated)</label><input class="input" id="m-states" value="q0, q1, q2" style="width:100%"/></div>
        <div class="form-group"><label>Input Alphabet</label><input class="input" id="m-input" value="a, b" style="width:100%"/></div>
        <div class="form-group"><label>Stack Alphabet</label><input class="input" id="m-stack" value="Z, A" style="width:100%"/></div>
        <div class="form-group"><label>Start State</label><input class="input" id="m-start" value="q0" style="width:100%"/></div>
        <div class="form-group"><label>Start Stack Symbol</label><input class="input" id="m-symbol" value="Z" style="width:100%"/></div>
        <div class="form-group"><label>Accept States</label><input class="input" id="m-accept" value="q2" style="width:100%"/></div>
      </div>
      <div class="form-group"><label>Transitions</label>
        <textarea class="input" id="m-trans" rows="6" style="min-height:120px">q0, a, Z, q0, AZ\nq0, a, A, q0, AA\nq0, b, A, q1, ε\nq1, b, A, q1, ε\nq1, ε, Z, q2, Z</textarea>
      </div>
      <div class="modal-actions">
        <button class="btn btn-icon" onclick="exportPDA()" title="Export JSON" style="margin-right:auto">⬇ Export JSON</button>
        <button class="btn btn-icon" onclick="document.getElementById('import-json').click()" title="Import JSON" style="margin-right:auto">⬆ Import JSON</button>
        <input type="file" id="import-json" style="display:none" accept=".json" onchange="importPDA(event)" />
        <button class="btn" onclick="closeModal()">Cancel</button>
        <button class="btn btn-primary" onclick="loadCustomPDA()">Load PDA</button>
      </div>`;
  } else {
    $('modal-content').innerHTML = `
      <h2>CFG → PDA Conversion</h2>
      <p class="form-hint">Enter productions: uppercase = variables, lowercase = terminals, ε = empty. Example: <code style="color:var(--cyan);font-family:var(--font-mono)">S -> aSb | ε</code></p>
      <div class="form-group"><label>Grammar Rules</label>
        <textarea class="input" id="m-cfg" rows="5" placeholder="S -> aSb | ε" style="min-height:100px">S -> aSb | ε</textarea>
      </div>
      <div class="modal-actions"><button class="btn" onclick="closeModal()">Cancel</button><button class="btn btn-primary" onclick="loadCustomCFG()">Convert & Load</button></div>`;
  }
}
function closeModal() { $('modal-overlay').style.display = 'none'; }

function loadCustomPDA() {
  try {
    const parse = s => s.split(',').map(x => x.trim()).filter(Boolean);
    const transLines = $('m-trans').value.split('\n').map(l => l.trim()).filter(l => l);

    // Basic validation
    const states = parse($('m-states').value);
    const inputAlphabet = parse($('m-input').value);
    const stackAlphabet = parse($('m-stack').value);
    const startState = $('m-start').value.trim();
    const startSymbol = $('m-symbol').value.trim();
    const acceptStates = parse($('m-accept').value);

    if (states.length === 0) throw new Error("States cannot be empty");
    if (!states.includes(startState)) throw new Error(`Start state '${startState}' is not in states list`);
    if (!stackAlphabet.includes(startSymbol)) throw new Error(`Start symbol '${startSymbol}' is not in stack alphabet`);

    const transitions = transLines.map((line, idx) => {
      const p = line.split(',').map(s => s.trim());
      if (p.length < 5) throw new Error(`Invalid transition format on line ${idx + 1}: ${line}`);

      const fromState = p[0], inputSymbol = p[1], popSymbol = p[2], toState = p[3], pushStr = p[4];

      if (!states.includes(fromState)) throw new Error(`Unknown fromState '${fromState}' on line ${idx + 1}`);
      if (!states.includes(toState)) throw new Error(`Unknown toState '${toState}' on line ${idx + 1}`);
      if (inputSymbol !== 'ε' && !inputAlphabet.includes(inputSymbol)) throw new Error(`Unknown input symbol '${inputSymbol}' on line ${idx + 1}`);
      if (popSymbol !== 'ε' && !stackAlphabet.includes(popSymbol)) throw new Error(`Unknown pop symbol '${popSymbol}' on line ${idx + 1}`);

      const pushSymbols = pushStr === 'ε' || pushStr === '' ? [] : pushStr.split('').filter(c => c !== ' ');
      pushSymbols.forEach(ps => { if (!stackAlphabet.includes(ps)) throw new Error(`Unknown push symbol '${ps}' on line ${idx + 1}`); });

      return { fromState, inputSymbol, popSymbol, toState, pushSymbols };
    }).filter(Boolean);

    pdaDef = { states, inputAlphabet, stackAlphabet, startState, startSymbol, acceptStates, transitions };
    const langInput = document.getElementById('custom-language');
    currentLanguage = langInput && langInput.value
      ? langInput.value
      : "Custom PDA";
    activeExId = null; engine = new PDAEngine({ ...pdaDef, acceptanceMode });
    simState = null; $('btn-run').disabled = false;
    closeModal(); renderExamples(); renderAll();
  } catch (e) {
    alert("Validation Error: " + e.message);
  }
}

function exportPDA() {
  if (!pdaDef) return alert("Load a PDA first before exporting");
  const dataStr = "data:text/json;charset=utf-8," + encodeURIComponent(JSON.stringify(pdaDef, null, 2));
  const dlNode = document.createElement('a');
  dlNode.setAttribute("href", dataStr);
  dlNode.setAttribute("download", "custom_pda.json");
  document.body.appendChild(dlNode); // required for firefox
  dlNode.click();
  dlNode.remove();
}

function importPDA(event) {
  const file = event.target.files[0];
  if (!file) return;
  const reader = new FileReader();
  reader.onload = function (e) {
    try {
      const def = JSON.parse(e.target.result);
      if (!def.states || !def.transitions) throw new Error("Invalid JSON structure");
      $('m-states').value = def.states.join(', ');
      $('m-input').value = def.inputAlphabet.join(', ');
      $('m-stack').value = def.stackAlphabet.join(', ');
      $('m-start').value = def.startState;
      $('m-symbol').value = def.startSymbol;
      $('m-accept').value = (def.acceptStates || []).join(', ');
      $('m-trans').value = def.transitions.map(t =>
        `${t.fromState}, ${t.inputSymbol}, ${t.popSymbol}, ${t.toState}, ${t.pushSymbols.length ? t.pushSymbols.join('') : 'ε'}`
      ).join('\n');
      $('pda-info').textContent = "JSON loaded. Click Load PDA";
    } catch (err) {
      alert("Error importing: " + err.message);
    }
  };
  reader.readAsText(file);
}

function loadCustomCFG() {
  try {
    const cfg = parseCFG($('m-cfg').value);
    pdaDef = cfgToPDA(cfg);
    currentLanguage = "Custom PDA";
    activeExId = null; engine = new PDAEngine({ ...pdaDef, acceptanceMode });
    simState = null; $('btn-run').disabled = false;
    closeModal(); renderExamples(); renderAll();
  } catch (e) { alert('Error: ' + e.message); }
}

// ─── Boot ────────────────────────────────────────
init();
