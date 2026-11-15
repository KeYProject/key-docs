/* Prism grammar for the KeY language (JavaDL terms, sequents and taclets).
 *
 * Decision: `key` is a real grammar rather than an alias of `jml`.
 * KeY shares JML's Java/JML annotation syntax (fenced `key` blocks are often
 * JavaDL terms or mixes of taclets and JML), so the grammar extends
 * `Prism.languages.jml` and adds the constructs that are KeY-specific:
 *
 *   - taclet structure keywords such as \schemaVar, \schemaVariables,
 *     \datatypes, \find, \assumes,
 *     \replacewith, \heuristics, \generate,
 *   - remaining backslash commands such as \forall, \exists, \old,
 *     \result, \subst, \if, \notFreeIn,
 *   - sequent arrows `==>`, `<==` and `<==>`,
 *   - schema variables such as `#cutFormula` and `#x`,
 *   - program modalities `\<...\>` and `\[...\]` (delimiters only; the
 *     enclosed program is Java source, not KeY syntax).
 *
 * The tokens are inserted after the string/char tokens (before `class-name`)
 * so that Java escape sequences inside strings (`"\n"`, `"\t"`) are not
 * mistaken for backslash commands.
 */
(function () {
  if (typeof Prism === 'undefined' || !Prism.languages.jml) {
    return;
  }

  Prism.languages.key = Prism.languages.extend('jml', {});

  Prism.languages.insertBefore('key', 'class-name', {
    'key-modality': /\\<|\\>|\\\[|\\\]/,
    'key-sequent-arrow': /<==>|==>|<==/,
    'key-schema-var': /#[A-Za-z_]\w*/,
    'key-taclet': /\\(?:schemaVariables|schemaVars?|datatypes?|sorts?|functions?|predicates?|rules?|axioms?|varcond|find|assumes|add|addProgVars|replacewith|closegoal|heuristics|noninteractive|displayname|helptext|generate|unique)\b/i,
    'key-command': /\\[a-zA-Z_]\w*/
  });
})();
