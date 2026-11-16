/* Kick off client-side highlighting after the deferred Prism bundle has run.
 * Every code block that should be coloured already carries a language-<x>
 * class; blocks without one are left untouched by Prism. */
(function (prism) {
  'use strict';

  if (typeof document === 'undefined' || !prism ||
      typeof prism.highlightAll !== 'function') {
    return;
  }

  prism.highlightAll();
})(typeof Prism === 'undefined' ? null : Prism);
