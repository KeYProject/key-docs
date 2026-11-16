/* Kick off client-side highlighting after the deferred Prism bundle has run.
 * Every code block that should be coloured already carries a language-<x>
 * class; blocks without one are left untouched by Prism. */
(function (prism) {
  'use strict';

  if (typeof document === 'undefined' || !prism ||
      typeof prism.highlightAll !== 'function') {
    return;
  }

  /* Multi-line JML annotations are inline spans after tokenisation, so their
   * background only covers the text. Turn them into blocks so the whole area
   * between `/*@` and `*\/` is filled. The first-line indentation is applied
   * with `text-indent`; continuation lines already carry their own leading
   * whitespace. Only annotations that start and end on their own line are
   * converted, so inline annotations keep the normal inline layout. */
  function markMultilineAnnotations() {
    var annotations = document.querySelectorAll('.token.jml-annotation');

    Array.prototype.forEach.call(annotations, function (annotation) {
      if (annotation.textContent.indexOf('\n') === -1) {
        return;
      }

      var code = annotation.closest('code');
      if (!code) {
        return;
      }

      var beforeRange = document.createRange();
      beforeRange.setStart(code, 0);
      beforeRange.setEnd(annotation, 0);
      var before = beforeRange.toString();
      var beforeLine = before.slice(before.lastIndexOf('\n') + 1);
      if (!/^[ \t]*$/.test(beforeLine)) {
        return;
      }

      var afterRange = document.createRange();
      afterRange.setStart(annotation, annotation.childNodes.length);
      afterRange.setEnd(code, code.childNodes.length);
      var afterLine = afterRange.toString().split('\n')[0];
      if (!/^[ \t]*$/.test(afterLine)) {
        return;
      }

      var indent = beforeLine.replace(/\t/g, '    ').length;

      /* Start the box at the code block's left edge so its background covers
       * the indentation and the full line width; text-indent puts the opening
       * delimiter back at its original column. */
      annotation.classList.add('jml-annotation--block');
      annotation.style.marginLeft = '-' + indent + 'ch';
      annotation.style.textIndent = indent + 'ch';
    });
  }

  prism.highlightAll();
  markMultilineAnnotations();
})(typeof Prism === 'undefined' ? null : Prism);
