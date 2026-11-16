/* Prism grammar for the KeY language (JavaDL terms, sequents and taclets).
 *
 * Decision: `key` is a real grammar rather than an alias of `jml`.
 * KeY files mix JavaDL terms, taclets and JML contracts, so the grammar
 * extends `Prism.languages.jml` and adds the constructs that are
 * KeY-specific:
 *
 *   - taclet, declaration, settings and variable-condition keywords from
 *     key.ncore/src/main/antlr/KeYLexer.g4 and
 *     key.core/src/main/antlr4/JavaKeYLexer.g4,
 *   - JML clause and modifier keywords at the top level, using the same
 *     vocabulary as prism-jml.js,
 *   - remaining backslash commands such as \forall, \exists, \sum and
 *     \seq_get,
 *   - sequent arrows `==>`, `<==`, `<==>` and `<=!=>`,
 *   - schema variables such as `#cutFormula` and `#x`,
 *   - program modalities `\<...\>`, `\diamond`, `\box`, `\endmodality`, …,
 *   - the JavaDL literals `TRUE` and `FALSE`.
 *
 * JML clauses are matched before Java keywords (`requires` is also a Java
 * keyword), while modifiers and the remaining tokens are inserted after the
 * keywords so `public` and `final` keep their Java colour.
 */
(function (prism) {
  'use strict';

  if (!prism || !prism.languages || !prism.languages.jml) {
    return;
  }

  var jmlKeywords = prism.jmlKeywords || { clause: [], declaration: [] };

  function wordPattern(words) {
    return new RegExp('\\b(?:' + words.join('|') + ')\\b');
  }

  /* Logic commands are deliberately not listed here: they fall through to
   * `key-command` and keep the generic command colour. */
  var tacletKeywords = [
    // Declarations and problem structure
    'sorts',
    'generic',
    'proxy',
    'extends',
    'oneof',
    'abstract',
    'alias',
    'schemaVariables',
    'schemaVar',
    'modalOperator',
    'program',
    'formula',
    'term',
    'update',
    'variables',
    'variable',
    'skolemTerm',
    'skolemFormula',
    'programVariables',
    'varcond',
    'applyUpdateOnRigid',
    'dropEffectlessElementaries',
    'simplifyIfThenElseUpdate',
    'hasSort',
    'isInductVar',
    'different',
    'sub',
    'equalUnique',
    'new',
    'newTypeOf',
    'hasElementarySort',
    'strict',
    'instantiateGeneric',
    'include',
    'includeLDTs',
    'programSource',
    'withOptions',
    'optionsDecl',
    'settings',
    'profile',
    // Taclet annotations and blocks
    'sameUpdateLevel',
    'ignoreUpdateLevel',
    'inSequentState',
    'antecedentPolarity',
    'succedentPolarity',
    'generate',
    'EQ',
    'closegoal',
    'heuristicsDecl',
    'noninteractive',
    'displayname',
    'helptext',
    'replacewith',
    'addrules',
    'addprogvars',
    'heuristics',
    'find',
    'add',
    'assumes',
    'trigger',
    'avoid',
    'predicates',
    'functions',
    'datatypes',
    'transformers',
    'unique',
    'free',
    'rules',
    'axioms',
    'problem',
    'proofObligation',
    'proof',
    'proofScript',
    'lemma',
    'termlabel',
    // File-level settings and contract selection
    'classpath',
    'bootclasspath',
    'noDefaultClasses',
    'javaSource',
    'chooseContract',
    'contracts',
    'invariants',
    'inType',
    'isAbstractOrInterface',
    'isFinal',
    'containerType',
    // Variable conditions (JavaKeYLexer.g4)
    'storeTermIn',
    'storeStmtIn',
    'hasInvariant',
    'getInvariant',
    'getFreeInvariant',
    'getVariant',
    'isLabeled',
    'sameObserver',
    'dependingOn',
    'disjointModuloNull',
    'dropEffectlessStores',
    'enumConstant',
    'freeLabelIn',
    'fieldType',
    'final',
    'elemSort',
    'hasLabel',
    'hasSubFormulas',
    'isArray',
    'isArrayLength',
    'isConstant',
    'isEnumType',
    'isLocalVariable',
    'isObserver',
    'metaDisjoint',
    'isThisReference',
    'differentFields',
    'isReference',
    'isReferenceArray',
    'isStaticField',
    'isModelField',
    'isInStrictFp',
    'newDependingOn',
    'newLocalVars',
    'newLabel',
    'containsAssignment',
    'hasAnnotation',
    'addAnnotation',
    'removeAnnotation',
    'notFreeIn',
    'static',
    'staticMethodReference',
    'mayExpandMethod'
  ];

  prism.languages.key = prism.languages.extend('jml', {});

  /* JML clauses are matched before Java keywords because `requires` is also a
   * Java keyword (module declarations). JML modifiers are matched after the
   * Java keywords, so words such as `public` and `final` keep their normal
   * Java colour. */
  prism.languages.insertBefore('key', 'keyword', {
    'key-jml-clause': wordPattern(jmlKeywords.clause)
  });

  prism.languages.insertBefore('key', 'boolean', {
    'key-modality': /\\<|\\>|\\\[|\\\]|\\(?:endmodality|diamond_transaction|box_transaction|throughout_transaction|diamond|box|throughout|modality)\b/,
    'key-sequent-arrow': /<==>|<=!=>|==>|<==/,

    'key-schema-var': /#[A-Za-z_]\w*/,
    'key-logic-literal': /\b(?:TRUE|FALSE)\b/,
    'key-jml-modifier': wordPattern(jmlKeywords.declaration),
    'key-taclet': new RegExp('\\\\(?:' + tacletKeywords.join('|') + ')\\b', 'i'),
    'key-command': /\\[a-zA-Z_]\w*/
  });
})(typeof Prism === 'undefined' ? null : Prism);
