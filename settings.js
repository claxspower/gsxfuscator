(() => {
  'use strict';
  const byId = id => document.getElementById(id);
  const key = 'clax.workspace.preferences';
  const photoKey = 'clax.workspace.photo';
  // One-way privacy migration: older builds saved entire generated scripts.
  // Do not create new build-history entries after this cleanup.
  try { localStorage.removeItem('clax_history_v7'); } catch { /* restricted storage */ }
  const nav = byId('workspace-nav');
  const navItems = new Map(Array.from(nav.querySelectorAll('[data-target]'), item => [item.dataset.target, item]));
  const tabs = Array.from(navItems.keys());
  // Graphite is the single, non-configurable palette. Only brightness changes.
  const MODES = new Set(['light', 'night']);
  function read(name) { try { return localStorage.getItem(name); } catch { return null; } }
  function save(name, value) {
    try {
      if (value === null) localStorage.removeItem(name);
      else localStorage.setItem(name, value);
      return true;
    } catch {
      byId('settings-status').textContent = 'Browser storage is unavailable or full. Changes apply to this visit.';
      return false;
    }
  }
  let stored;
  try { stored = JSON.parse(read(key)); } catch { /* Fall back to the defaults. */ }
  if (!stored || typeof stored !== 'object') stored = {};
  const order = Array.isArray(stored.order) ? stored.order : [];
  const prefs = {
    mode: MODES.has(stored.mode) ? stored.mode : 'night',
    largeText: stored.largeText === true,
    start: navItems.has(stored.start) ? stored.start : 'overview',
    lastTab: navItems.has(stored.lastTab) ? stored.lastTab : null,
    order: Array.from(new Set(order.concat(tabs).filter(tab => navItems.has(tab)))),
    name: typeof stored.name === 'string' ? stored.name.slice(0,48) : '',
    username: typeof stored.username === 'string' ? stored.username.slice(0,32) : '',
  };
  const persist = () => save(key, JSON.stringify(prefs));
  const status = message => { byId('settings-status').textContent = message; };
  function applyAppearance() {
    const root = document.documentElement;
    root.dataset.theme = 'graphite';
    root.dataset.mode = prefs.mode;
    root.dataset.textSize = prefs.largeText ? 'large' : 'standard';
    const bar = byId('clax-theme-color');
    if (bar) bar.content = prefs.mode === 'light' ? '#f7f9fc' : '#0c1118';
    for (const button of document.querySelectorAll('[data-mode-choice]')) {
      const selected = button.dataset.modeChoice === prefs.mode;
      button.setAttribute('aria-pressed', String(selected));
    }
    byId('large-text-toggle').checked = prefs.largeText;
  }
  byId('mode-control').addEventListener('click', event => {
    const button = event.target.closest('[data-mode-choice]');
    if (!button || !MODES.has(button.dataset.modeChoice)) return;
    if (prefs.mode === button.dataset.modeChoice) return;
    prefs.mode = button.dataset.modeChoice;
    applyAppearance();
    persist();
    status('Graphite ' + (prefs.mode === 'light' ? 'Light' : 'Night') + ' mode enabled.');
  });
  byId('large-text-toggle').addEventListener('change', event => {
    prefs.largeText = event.target.checked;
    applyAppearance();
    persist();
    status(prefs.largeText ? 'Larger reading text enabled.' : 'Standard reading text enabled.');
  });
  applyAppearance();
  // Privacy/accessibility migration: discard obsolete theme/font fields once.
  if (Object.prototype.hasOwnProperty.call(stored, 'font') ||
      Object.prototype.hasOwnProperty.call(stored, 'theme')) persist();

  let photo = read(photoKey) || '';
  if (photo.length > 160000 || !/^data:image\/jpeg;base64,[a-zA-Z0-9+/=]+$/.test(photo)) photo = '';
  function applyProfile() {
    const name = prefs.name.trim() || 'GsX User';
    byId('profile-name').textContent = name;
    byId('overview-profile-name').textContent = name;
    byId('profile-handle').textContent = '@' + (prefs.username.trim().replace(/^@+/, '') || 'gsxuser');
    const initials = name.split(/\s+/u).slice(0,2).map(word => Array.from(word)[0]).join('').toUpperCase();
    for (const avatar of document.querySelectorAll('[data-avatar]')) {
      if (photo) {
        if (avatar.firstElementChild?.getAttribute('src') === photo) continue;
        const img = new Image();
        img.alt = '';
        img.src = photo;
        avatar.replaceChildren(img);
      } else avatar.textContent = initials;
    }
    byId('remove-photo').hidden = !photo;
  }
  for (const field of ['name','username']) {
    const input = byId('setting-' + field);
    input.value = prefs[field];
    input.addEventListener('input', () => { prefs[field] = input.value; applyProfile(); persist(); });
  }
  applyProfile();
  let photoRevision = 0;
  byId('profile-file').addEventListener('change', async event => {
    const file = event.target.files[0];
    if (!file) return;
    const revision = ++photoRevision;
    event.target.value = '';
    if (!['image/jpeg','image/png','image/webp'].includes(file.type) || file.size > 8 * 1024 * 1024) {
      status('Choose a JPG, PNG or WebP image up to 8 MB.'); return;
    }
    // Store a small, square thumbnail. FileReader works under the dashboard's data-only image policy.
    try {
      const url = await new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = () => resolve(reader.result);
        reader.onerror = reject;
        reader.readAsDataURL(file);
      });
      if (revision !== photoRevision) return;
      const image = new Image();
      const decoded = new Promise((resolve, reject) => { image.onload = resolve; image.onerror = reject; });
      image.src = url;
      await decoded;
      if (revision !== photoRevision) return;
      const canvas = document.createElement('canvas');
      canvas.width = canvas.height = 144;
      const side = Math.min(image.naturalWidth, image.naturalHeight);
      const ctx = canvas.getContext('2d');
      ctx.fillStyle = '#19191d';
      ctx.fillRect(0,0,144,144);
      ctx.drawImage(image,(image.naturalWidth-side)/2,(image.naturalHeight-side)/2,side,side,0,0,144,144);
      photo = canvas.toDataURL('image/jpeg', .82);
      applyProfile();
      if (save(photoKey, photo)) status('Profile photo saved.');
    } catch {
      if (revision === photoRevision) status('This photo could not be opened. Choose another image.');
    }
  });
  byId('remove-photo').addEventListener('click', () => {
    photoRevision++;
    photo = '';
    applyProfile();
    if (save(photoKey, null)) status('Profile photo removed.');
  });

  const list = byId('tab-order');
  function moveTo(tab, position) {
    const old = prefs.order.indexOf(tab);
    if (old < 0 || old === position || position < 0 || position >= prefs.order.length) return;
    prefs.order.splice(old, 1);
    prefs.order.splice(position, 0, tab);
    renderOrder();
    if (persist()) status(navItems.get(tab).textContent.trim() + ' moved to position ' + (position + 1) + '.');
  }
  function renderOrder() {
    list.replaceChildren();
    prefs.order.forEach((tab, index) => {
      const item = navItems.get(tab);
      nav.append(item);
      const row = document.createElement('li');
      row.dataset.orderTab = tab;
      row.draggable = true;
      const title = item.textContent.trim();
      const grip = document.createElement('span');
      grip.className = 'tab-grip';
      grip.setAttribute('aria-hidden', 'true');
      grip.textContent = '⠿';
      const label = document.createElement('span');
      label.className = 'order-title';
      label.textContent = title;
      row.append(grip, label);
      for (const [delta, direction, symbol] of [[-1,'up','↑'],[1,'down','↓']]) {
        const button = document.createElement('button');
        button.type = 'button';
        button.dataset.direction = direction;
        button.setAttribute('aria-label', 'Move ' + title + ' ' + direction);
        button.textContent = symbol;
        const next = index + delta;
        button.disabled = next < 0 || next >= prefs.order.length;
        button.addEventListener('click', () => {
          moveTo(tab, next);
          const movedRow = list.children[next];
          const sameDirection = movedRow.querySelector('[data-direction="' + direction + '"]');
          (sameDirection.disabled ? movedRow.querySelector('button:enabled') : sameDirection)?.focus();
        });
        row.append(button);
      }
      list.append(row);
    });
  }
  let dragged = '';
  for (const container of [nav, list]) {
    const getRow = event => event.target.closest('[data-order-tab],[data-target]');
    const clearHover = () => container.querySelector('.drag-over')?.classList.remove('drag-over');
    container.addEventListener('dragstart', event => {
      const row = getRow(event);
      dragged = row?.dataset.orderTab || row?.dataset.target || '';
      if (!navItems.has(dragged)) return;
      event.dataTransfer.setData('text/plain', dragged);
      event.dataTransfer.effectAllowed = 'move';
    });
    container.addEventListener('dragover', event => {
      const row = getRow(event);
      if (!dragged || !row) return;
      event.preventDefault();
      event.dataTransfer.dropEffect = 'move';
      clearHover();
      row.classList.add('drag-over');
    });
    container.addEventListener('drop', event => {
      const row = getRow(event);
      if (!dragged || !row) return;
      event.preventDefault();
      clearHover();
      moveTo(dragged, prefs.order.indexOf(row.dataset.orderTab || row.dataset.target));
      dragged = '';
    });
    container.addEventListener('dragend', () => {
      dragged = '';
      nav.querySelector('.drag-over')?.classList.remove('drag-over');
      list.querySelector('.drag-over')?.classList.remove('drag-over');
    });
  }
  for (const [tab, item] of navItems) {
    byId('setting-start').add(new Option(item.textContent.trim(), tab));
    item.draggable = true;
    if (item.classList.contains('active')) item.setAttribute('aria-current', 'page');
    if (item.matches('a:not([href])')) {
      item.setAttribute('role', 'button');
      item.tabIndex = 0;
      item.addEventListener('keydown', event => {
        if (event.key === 'Enter' || event.key === ' ') { event.preventDefault(); item.click(); }
      });
    }
  }
  renderOrder();
  byId('setting-start').value = prefs.start;
  byId('setting-start').addEventListener('change', event => { prefs.start = event.target.value; persist(); });
  window.ClaxRememberTab = function(tab) {
    if (navItems.has(tab) && prefs.lastTab !== tab) {
      prefs.lastTab = tab;
      persist();
    }
  };
  // Restore actual last tab where possible, otherwise the chosen start tab.
  if (!docsFragment()) switchTab(prefs.lastTab || prefs.start);
})();
