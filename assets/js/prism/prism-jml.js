/* Original Prism grammar for JML, written for the KeY documentation.
 * Keyword lists derived from the JML Reference Manual and KeY's JML dialect.
 * The JMLtk project's grammar was consulted as a design reference only; no
 * upstream code is copied and no upstream licence is asserted.
 *
 * JML source is Java source with specification text in `/*@ ... @*\/`,
 * `//@ ...` and `//+tool@ ...` comments. The grammar therefore starts from
 * Prism's Java grammar and adds the specification delimiters and the JML
 * vocabulary; everything outside an annotation keeps Java highlighting.
 */
(function (prism) {
  'use strict';

  if (!prism || !prism.languages || !prism.languages.java) {
    return;
  }

  var java = prism.languages.java;

  /* Vocabulary, grouped by the token each word belongs to. */
  var behaviourKeywords = [
    'behavior',
    'normal_behavior',
    'exceptional_behavior',
    'abrupt_behavior',
    'break_behavior',
    'continue_behavior',
    'return_behavior',
    'feasible_behavior',
    'model_behavior',
    'also'
  ];

  var clauseKeywords = [
    'requires',
    'requires_free',
    'requires_redundantly',
    'ensures',
    'ensures_free',
    'ensures_redundantly',
    'pre',
    'pre_redundantly',
    'post',
    'post_redundantly',
    'old',
    'forall',
    'assignable',
    'assignable_redundantly',
    'modifiable',
    'modifiable_redundantly',
    'modifies',
    'modifies_redundantly',
    'accessible',
    'accessible_redundantly',
    'captures',
    'captures_redundantly',
    'working_space',
    'working_space_redundantly',
    'duration',
    'duration_redundantly',
    'signals',
    'signals_only',
    'signals_redundantly',
    'when',
    'callable',
    'callable_redundantly',
    'diverges',
    'diverges_redundantly',
    'loop_invariant',
    'loop_invariant_free',
    'loop_invariant_redundantly',
    'maintaining',
    'maintaining_redundantly',
    'decreases',
    'decreases_redundantly',
    'decreasing',
    'measured_by',
    'returns',
    'returns_redundantly',
    'breaks',
    'breaks_redundantly',
    'continues',
    'continues_redundantly',
    'determines',
    'loop_determines',
    'separates',
    'loop_separates'
  ];

  var declarationKeywords = [
    'invariant',
    'constraint',
    'initially',
    'axiom',
    'represents',
    'model',
    'ghost',
    'pure',
    'helper',
    'nullable',
    'non_null',
    'spec_public',
    'spec_protected',
    'code',
    'monitored',
    'uninitialized',
    'readonly',
    'static_initializer',
    'two_state',
    'no_state',
    'function',
    'lemma',
    'merge_point',
    'refining',
    'assert',
    'assume',
    'set',
    'unreachable',
    'reachable',
    'debug',
    'nowarn',
    'public',
    'private',
    'protected',
    'package'
  ];

  var commandKeywords = [
    'result',
    'old',
    'forall',
    'exists',
    'sum',
    'product',
    'bsum',
    'bigsum',
    'num_of',
    'min',
    'max',
    'if',
    'then',
    'else',
    'let',
    'in',
    'type',
    'typeof',
    'elemtype',
    'nonnullelements',
    'invariant_for',
    'reach',
    'fresh',
    'not_modified',
    'nothing',
    'everything',
    'such_that',
    'lbl',
    'lblneg',
    'lblpos',
    'duration',
    'working_space',
    'space',
    'values',
    'lock',
    'unlock',
    'is_initialized',
    'same',
    'seq_union',
    'seq_prepend',
    'seq_concat',
    'seq_reverse',
    'seq_subsequence',
    'onlyAccessed',
    'onlyAssigned',
    'onlyCaptured',
    'onlyErased'
  ];

  function wordPattern(words) {
    return new RegExp('\\b(?:' + words.join('|') + ')\\b');
  }

  function commandPattern(words) {
    return new RegExp('\\\\' + '(?:' + words.join('|') + ')\\b');
  }

  /* Tokens used inside an annotation. Java tokens are reused by reference so
   * strings, literals, operators and Java names keep their usual colours. */
  var annotationBody = {
    'jml-delimiter': {
      pattern: /\/(?:\*|\/)[-+]?[\w+,-]*@|@\*\/|(?:^|\n)[ \t]*@(?=[ \t])/,
      alias: 'comment'
    },
    'string': java.string,
    'char': java.char,
    'jml-command': commandPattern(commandKeywords),
    'jml-behavior': wordPattern(behaviourKeywords),
    'jml-clause': wordPattern(clauseKeywords),
    'jml-declaration': wordPattern(declarationKeywords),
    'number': java.number,
    'boolean': java.boolean,
    'operator': java.operator,
    'punctuation': java.punctuation,
    'class-name': java['class-name']
  };

  var annotationTokens = {
    'jml-annotation': {
      pattern: /\/\*[-+]?[\w+,-]*@[\s\S]*?\*\//,
      greedy: true,
      inside: annotationBody
    },
    'jml-line': {
      pattern: /\/\/[-+]?[\w+,-]*@[^\n]*/,
      greedy: true,
      inside: annotationBody
    }
  };

  /* Java grammar plus the annotation tokens in front of Java's own comment
   * token, which would otherwise swallow `/*@` and `//@` first. */
  var javaGrammar = prism.languages.extend('java', {});
  var grammar = {};

  Object.keys(annotationTokens).forEach(function (name) {
    grammar[name] = annotationTokens[name];
  });
  Object.keys(javaGrammar).forEach(function (name) {
    grammar[name] = javaGrammar[name];
  });

  prism.languages.jml = grammar;
})(typeof Prism === 'undefined' ? null : Prism);
