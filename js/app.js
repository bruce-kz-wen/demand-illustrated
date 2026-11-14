/*
 * Tabs. Each illustration is a button in the header (data-tab="name") and a
 * section with the id "panel-name". Its script calls App.register("name", start),
 * and start(panel) runs the first time the tab is shown.
 */
(function () {
  'use strict';
  const starters = {}, started = new Set();
  let tabs = [];

  function show(name, fromUser) {
    for (const tab of tabs) {
      const on = tab.dataset.tab === name;
      tab.setAttribute('aria-selected', String(on));
      tab.tabIndex = on ? 0 : -1;
      document.getElementById('panel-' + tab.dataset.tab).hidden = !on;
    }
    if (starters[name] && !started.has(name)) {
      started.add(name);
      starters[name](document.getElementById('panel-' + name));
    }
    if (fromUser) history.replaceState(null, '', '#' + name);
  }

  window.App = { register(name, start) { starters[name] = start; } };

  document.addEventListener('DOMContentLoaded', () => {
    document.querySelectorAll('.tex').forEach((el) => Viz.tex(el, el.textContent, el.classList.contains('display')));
    document.getElementById('theme-toggle').addEventListener('click', Viz.toggleTheme);
    tabs = Array.from(document.querySelectorAll('.tabs [role="tab"]'));
    tabs.forEach((tab, i) => {
      tab.addEventListener('click', () => show(tab.dataset.tab, true));
      tab.addEventListener('keydown', (event) => {
        const step = event.key === 'ArrowRight' ? 1 : event.key === 'ArrowLeft' ? -1 : 0;
        if (!step) return;
        const next = tabs[(i + step + tabs.length) % tabs.length];
        next.focus();
        show(next.dataset.tab, true);
      });
    });
    const wanted = location.hash.slice(1);
    show(tabs.some((tab) => tab.dataset.tab === wanted) ? wanted : tabs[0].dataset.tab, false);
  });
})();
