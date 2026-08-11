---
title: JSON RPC 
---

# JSON RPC 

work in progress and automatically generated. 

## General Notes 



## Types
### Type: ContractDesc
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type ContractDesc {
   /*  */
  contractId : ContractId
  /*  */
  displayName : STRING
  /*  */
  htmlText : STRING
  /*  */
  name : STRING
  /*  */
  plainText : STRING
  /*  */
  typeName : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: ContractId
[@author Alexander Weigl, @version 1 (28.10.23)][]
```
type ContractId {
   /*  */
  contractId : STRING
  /*  */
  envId : EnvironmentId
}
```
[@author Alexander Weigl, @version 1 (28.10.23)][]
### Type: EnvironmentId
[@author Alexander Weigl, @version 1 (28.10.23)][]
```
type EnvironmentId {
   /*  */
  envId : STRING
}
```
[@author Alexander Weigl, @version 1 (28.10.23)][]
### Type: ExampleDesc
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type ExampleDesc {
   /*  */
  description : STRING
  /*  */
  name : STRING
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: FunctionDesc
[@author Alexander Weigl, @version 1 (15.10.23)][]
```
type FunctionDesc {
   /*  */
  argSorts : SortDesc[]
  /*  */
  name : STRING
  /*  */
  retSort : SortDesc
  /*  */
  rigid : BOOL
  /*  */
  skolemConstant : BOOL
  /*  */
  sort : STRING
  /*  */
  unique : BOOL
}
```
[@author Alexander Weigl, @version 1 (15.10.23)][]
### Type: LoadParams
[][]
```
type LoadParams {
   /*  */
  bootClassPath : Path
  /*  */
  classPath : Path[]
  /*  */
  includes : Path[]
  /*  */
  problemFile : Path
}
```
[][]
### Type: LogTraceParams

```
type LogTraceParams {
   /*  */
  messag : STRING
  /*  */
  verbose : STRING
}
```

### Type: MacroStatistic
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type MacroStatistic {
   /*  */
  appliedRules : INT
  /*  */
  closedGoals : INT
  /*  */
  macroId : STRING
  /*  */
  proofId : ProofId
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: MessageActionItem

```
type MessageActionItem {
   /*  */
  title : STRING
}
```

### Type: NodeDesc
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type NodeDesc {
   /*  */
  branchLabel : STRING
  /*  */
  children : NodeDesc[]
  /*  */
  description : STRING
  /*  */
  nodeid : NodeId
  /*  */
  scriptRuleApplication : BOOL
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: NodeId
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type NodeId {
   /*  */
  nodeId : INT
  /*  */
  proofId : ProofId
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: NodeTextDesc
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type NodeTextDesc {
   /*  */
  id : NodeTextId
  /*  */
  result : STRING
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: NodeTextId
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type NodeTextId {
   /*  */
  nodeId : NodeId
  /*  */
  nodeTextId : INT
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: PrintOptions
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type PrintOptions {
   /*  */
  indentation : INT
  /*  */
  pure : BOOL
  /*  */
  termLabels : BOOL
  /*  */
  unicode : BOOL
  /*  */
  width : INT
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: ProblemDefinition
[@author Alexander Weigl, @version 1 (15.10.23)][]
```
type ProblemDefinition {
   /*  */
  antecTerms : STRING[]
  /*  */
  functions : FunctionDesc[]
  /*  */
  predicates : PredicateDesc[]
  /*  */
  sorts : SortDesc[]
  /*  */
  succTerms : STRING[]
}
```
[@author Alexander Weigl, @version 1 (15.10.23)][]
### Type: ProofId

```
type ProofId {
   /*  */
  env : EnvironmentId
  /*  */
  proofId : STRING
}
```

### Type: ProofMacroDesc
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type ProofMacroDesc {
   /*  */
  category : STRING
  /*  */
  description : STRING
  /*  */
  name : STRING
  /*  */
  scriptCommandName : STRING
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: ProofScriptCommandDesc
[@author Alexander Weigl, @version 1 (29.10.23)][]
```
type ProofScriptCommandDesc {
   /*  */
  documentation : STRING
  /*  */
  macroId : STRING
}
```
[@author Alexander Weigl, @version 1 (29.10.23)][]
### Type: ProofStatus

```
type ProofStatus {
   /*  */
  closedGoals : INT
  /*  */
  id : ProofId
  /*  */
  openGoals : INT
}
```

### Type: SetTraceParams
[][]
```
type SetTraceParams {
   /* The new value that should be assigned to the trace setting. */
  value : TraceValue
}
```
[][]
### Type: ShowDocumentParams
[][]
```
type ShowDocumentParams {
   /*  */
  external : BOOL
  /*  */
  selection : TextRange
  /*  */
  takeFocus : BOOL
  /*  */
  uri : STRING
}
```
[][]
### Type: ShowDocumentResult

```
type ShowDocumentResult {
   /*  */
  success : BOOL
}
```

### Type: ShowMessageParams

```
type ShowMessageParams {
   /*  */
  message : STRING
  /*  */
  type : MessageType
}
```

### Type: ShowMessageRequestParams

```
type ShowMessageRequestParams {
   /*  */
  actions : MessageActionItem[]
  /*  */
  message : STRING
  /*  */
  type : MessageType
}
```

### Type: SortDesc
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type SortDesc {
   /*  */
  anAbstract : BOOL
  /*  */
  documentation : STRING
  /*  */
  extendsSorts : SortDesc[]
  /*  */
  s : STRING
  /*  */
  string : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: StrategyOptions
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type StrategyOptions {
   /*  */
  dep : STRING
  /*  */
  maxSteps : INT
  /*  */
  method : STRING
  /*  */
  nonLinArith : STRING
  /*  */
  query : STRING
  /*  */
  stopMode : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: TaskFinishedInfo

```
type TaskFinishedInfo {
   /*  */
  appliedRules : INT
  /*  */
  closedGoals : INT
  /*  */
  time : LONG
}
```

### Type: TaskStartedInfo

```
type TaskStartedInfo {
   /*  */
  kind : TaskKind
  /*  */
  message : STRING
  /*  */
  size : INT
}
```

### Type: TermActionDesc
This class represents an action that can be executed on a term.[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type TermActionDesc {
   /*  */
  category : STRING
  /*  */
  commandId : TermActionId
  /*  */
  description : STRING
  /*  */
  displayName : STRING
  /*  */
  kind : TermActionKind
}
```
This class represents an action that can be executed on a term.[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: TermActionId
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type TermActionId {
   /*  */
  id : STRING
  /*  */
  nodeId : NodeId
  /*  */
  pio : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: TreeNodeDesc
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type TreeNodeDesc {
   /*  */
  id : NodeId
  /*  */
  name : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
### Type: TreeNodeId
[@author Alexander Weigl, @version 1 (13.10.23)][]
```
type TreeNodeId {
   /*  */
  id : STRING
}
```
[@author Alexander Weigl, @version 1 (13.10.23)][]
## Endpoints
### client/logTrace (`server ~~> client`) 

```
Client.client/logTrace( params : LogTraceParams ) **async**
```
[][]

### client/sayHello (`server ~~> client`) 

```
Client.client/sayHello( e : STRING ) **async**
```
[][]

### client/showDocument (`server -> client`) 

```
Client.client/showDocument( params : ShowDocumentParams ) -> ShowDocumentResult
```
[][]

### client/sm (`server ~~> client`) 

```
Client.client/sm( params : ShowMessageParams ) **async**
```
[][]

### client/taskFinished (`server ~~> client`) 

```
Client.client/taskFinished( info : TaskFinishedInfo ) **async**
```
[][]

### client/taskProgress (`server ~~> client`) 

```
Client.client/taskProgress( position : INT ) **async**
```
[][]

### client/taskStarted (`server ~~> client`) 

```
Client.client/taskStarted( info : TaskStartedInfo ) **async**
```
[][]

### client/userResponse (`server -> client`) 

```
Client.client/userResponse( params : ShowMessageRequestParams ) -> MessageActionItem
```
[][]

### env/contracts (`client -> server`) 

```
Server.env/contracts( env : EnvironmentId ) -> ContractDesc[]
```
[][]

### env/dispose (`client -> server`) 

```
Server.env/dispose( env : EnvironmentId ) -> BOOL
```
[][]

### env/functions (`client -> server`) 

```
Server.env/functions( env : EnvironmentId ) -> FunctionDesc[]
```
[][]

### env/openContract (`client -> server`) 

```
Server.env/openContract( contractId : ContractId ) -> ProofId
```
[][]

### env/sorts (`client -> server`) 

```
Server.env/sorts( env : EnvironmentId ) -> SortDesc[]
```
[][]

### examples/list (`client -> server`) 

```
Server.examples/list(  ) -> ExampleDesc[]
```
[][]

### goal/actions (`client -> server`) 

```
Server.goal/actions( id : NodeTextId, pos : INT ) -> TermActionDesc[]
```
[][]

### goal/apply_action (`client -> server`) 

```
Server.goal/apply_action( id : TermActionId ) -> TermActionDesc[]
```
[][]

### goal/free (`client ~~> server`) 

```
Server.goal/free( id : NodeTextId ) **async**
```
[][]

### goal/print (`client -> server`) 

```
Server.goal/print( id : NodeId, options : PrintOptions ) -> NodeTextDesc
```
[][]

### loading/load (`client -> server`) 

```
Server.loading/load( params : LoadParams ) -> either<a,b>
```
[params parameters for loading][com.github.therapi.runtimejavadoc.ThrowsJavadoc@3c9d0b9d]

### loading/loadExample (`client -> server`) 

```
Server.loading/loadExample( id : STRING ) -> ProofId
```
[id ][]

### loading/loadKey (`client -> server`) 

```
Server.loading/loadKey( content : STRING ) -> ProofId
```
[][]

### loading/loadProblem (`client -> server`) 

```
Server.loading/loadProblem( problem : ProblemDefinition ) -> ProofId
```
[][]

### loading/loadTerm (`client -> server`) 

```
Server.loading/loadTerm( term : STRING ) -> ProofId
```
[][]

### meta/available_macros (`client -> server`) 

```
Server.meta/available_macros(  ) -> ProofMacroDesc[]
```
[][]

### meta/available_script_commands (`client -> server`) 

```
Server.meta/available_script_commands(  ) -> ProofScriptCommandDesc[]
```
[][]

### meta/version (`client -> server`) 

```
Server.meta/version(  ) -> STRING
```
[][]

### proof/auto (`client -> server`) 

```
Server.proof/auto( proof : ProofId, options : StrategyOptions ) -> ProofStatus
```
[][]

### proof/children (`client -> server`) 

```
Server.proof/children( nodeId : NodeId ) -> NodeDesc[]
```
[][]

### proof/dispose (`client -> server`) 

```
Server.proof/dispose( proof : ProofId ) -> BOOL
```
[][]

### proof/goals (`client -> server`) 

```
Server.proof/goals( proof : ProofId, onlyOpened : BOOL, onlyEnabled : BOOL ) -> NodeDesc[]
```
[][]

### proof/macro (`client -> server`) 

```
Server.proof/macro( proof : ProofId, macroName : STRING, options : StrategyOptions ) -> MacroStatistic
```
[][]

### proof/pruneTo (`client -> server`) 

```
Server.proof/pruneTo( nodeId : NodeId ) -> NodeDesc[]
```
[][]

### proof/root (`client -> server`) 

```
Server.proof/root( proof : ProofId ) -> NodeDesc
```
[][]

### proof/script (`client -> server`) 

```
Server.proof/script( proof : ProofId, scriptLine : STRING, options : StrategyOptions ) -> MacroStatistic
```
[][]

### proof/tree (`client -> server`) 

```
Server.proof/tree( proof : ProofId ) -> NodeDesc
```
[][]

### proofTree/children (`client -> server`) 

```
Server.proofTree/children( proof : ProofId, nodeId : TreeNodeId ) -> TreeNodeDesc[]
```
[][]

### proofTree/root (`client -> server`) 

```
Server.proofTree/root( id : ProofId ) -> TreeNodeDesc
```
[][]

### proofTree/subtree (`client -> server`) 

```
Server.proofTree/subtree( proof : ProofId, nodeId : TreeNodeId ) -> TreeNodeDesc[]
```
[][]

### server/exit (`client ~~> server`) 

```
Server.server/exit(  ) **async**
```
[][]

### server/setTrace (`client ~~> server`) 

```
Server.server/setTrace( params : SetTraceParams ) **async**
```
[][]

### server/shutdown (`client -> server`) 

```
Server.server/shutdown(  ) -> BOOL
```
[][]

