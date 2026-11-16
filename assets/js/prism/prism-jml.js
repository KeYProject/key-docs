/* Original Prism grammar for JML, written for the KeY documentation.
 * Keyword lists derived from the JML Reference Manual and KeY's JML dialect.
 * The JMLtk project's grammar was consulted as a design reference only; no
 * upstream code is copied and no upstream licence is asserted.
 *
 * JML source is Java source with specification text in `/*@ ... *\/`,
 * `/*@ ... @*\/`, `//@ ...` and `//+tool@ ...` comments. The grammar
 * therefore starts from Prism's Java grammar and adds the specification
 * delimiters and the JML vocabulary; everything outside an annotation keeps
 * Java highlighting.
 */
(function (prism) {
  'use strict';

  if (!prism || !prism.languages || !prism.languages.java) {
    return;
  }

  var java = prism.languages.java;

  /* Vocabulary, grouped by the token each word belongs to. */
  /* Keyword lists follow the JML lexer in KeY
   * (key.core/src/main/antlr4/JmlLexer.g4). The lexer allows most clause
   * keywords to carry a `_free` or `_redundantly` suffix; both forms are
   * listed so highlighting does not depend on the exact spelling. */

  var behaviourKeywords = [
    'behavior',
    'behaviour',
    'also',
    'abrupt_behavior',
    'break_behavior',
    'continue_behavior',
    'exceptional_behavior',
    'feasible_behavior',
    'model_behavior',
    'normal_behavior',
    'return_behavior'
  ];

  function clauseForms(words) {
    var forms = [];
    words.forEach(function (word) {
      forms.push(word, word + '_free', word + '_redundantly');
    });
    return forms;
  }

  var clauseKeywords = clauseForms([
    'accessible',
    'assert',
    'assume',
    'assignable',
    'assigns',
    'assigning',
    'captures',
    'constraint',
    'decreasing',
    'decreases',
    'diverges',
    'ensures',
    'exsures',
    'in',
    'invariant',
    'loop_assignable',
    'loop_assigns',
    'loop_assigning',
    'loop_invariant',
    'loop_modifiable',
    'loop_modifies',
    'loop_modifying',
    'loop_variant',
    'loop_writable',
    'loop_writes',
    'loop_writing',
    'maintaining',
    'maps',
    'measured_by',
    'modifiable',
    'modifies',
    'modifying',
    'post',
    'pre',
    'represents',
    'requires',
    'signals',
    'signals_only',
    'when',
    'working_space',
    'writable',
    'writes',
    'writing'
  ]).concat([
    'axiom',
    'breaks',
    'continues',
    'determines',
    'for_example',
    'implies_that',
    'initially',
    'loop_contract',
    'loop_determines',
    'loop_separates',
    'merge_params',
    'monitors_for',
    'returns',
    'separates',
    'set'
  ]);

  var declarationKeywords = [
    'abstract',
    'also',
    'code',
    'code_bigint_math',
    'code_java_math',
    'code_safe_math',
    'const',
    'debug',
    'final',
    'function',
    'ghost',
    'helper',
    'instance',
    'lemma',
    'merge_point',
    'merge_proc',
    'model',
    'model_method_axiom',
    'monitored',
    'name',
    'native',
    'no_state',
    'non_null',
    'nowarn',
    'nullable',
    'nullable_by_default',
    'package',
    'private',
    'protected',
    'public',
    'pure',
    'readable',
    'readonly',
    'reachable',
    'refining',
    'spec_bigint_math',
    'spec_java_math',
    'spec_protected',
    'spec_public',
    'spec_safe_math',
    'static',
    'static_initializer',
    'strictfp',
    'strictly_pure',
    'synchronized',
    'transient',
    'two_state',
    'uninitialized',
    'unreachable',
    'var',
    'volatile'
  ];

  var commandKeywords = [
    'all_fields',
    'all_objects',
    'backup',
    'before',
    'bigint',
    'bigint_math',
    'bigsum',
    'bsum',
    'by',
    'declassifies',
    'disjoint',
    'domain_implies_created',
    'duration',
    'elemtype',
    'else',
    'empty',
    'erases',
    'everything',
    'exception',
    'exists',
    'forall',
    'fp_abs',
    'fp_infinite',
    'fp_nan',
    'fp_negative',
    'fp_nice',
    'fp_normal',
    'fp_positive',
    'fp_subnormal',
    'fp_zero',
    'free',
    'fresh',
    'from_goal',
    'if',
    'in',
    'in_domain',
    'index',
    'infinite_union',
    'intersect',
    'into',
    'inv',
    'inv_free',
    'invariant_for',
    'invariant_free_for',
    'is_finite',
    'is_initialized',
    'itself',
    'java_math',
    'lbl',
    'lblneg',
    'lblpos',
    'let',
    'lock',
    'lockset',
    'locset',
    'map',
    'map_empty',
    'map_get',
    'map_override',
    'map_remove',
    'map_singleton',
    'map_size',
    'map_update',
    'max',
    'measured_by',
    'min',
    'new_elems_fresh',
    'new_objects',
    'nonnullelements',
    'not_assigned',
    'not_modified',
    'not_specified',
    'nothing',
    'num_of',
    'old',
    'onlyAccessed',
    'onlyAssigned',
    'onlyCaptured',
    'onlyErased',
    'permission',
    'pre',
    'product',
    'reach',
    'reachLocs',
    'real',
    'result',
    'safe_math',
    'same',
    'seq',
    'seq_2_map',
    'seq_concat',
    'seq_def',
    'seq_empty',
    'seq_get',
    'seq_prepend',
    'seq_reverse',
    'seq_singleton',
    'seq_sub',
    'seq_subsequence',
    'seq_union',
    'seq_upd',
    'seq_indexOf',
    'set_minus',
    'set_union',
    'singleton',
    'space',
    'static_invariant_for',
    'static_invariant_free_for',
    'storeref',
    'strictly_nothing',
    'string_equal',
    'subset',
    'such_that',
    'sum',
    'then',
    'transactionUpdated',
    'transient',
    'type',
    'TYPE',
    'typeof',
    'unlock',
    'values',
    'working_space'
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
      pattern: /\/(?:\*|\/)[-+]?[\w+,-]*@|@\*\/|\*\/|(?:^|\n)[ \t]*@(?=[ \t])/,
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
