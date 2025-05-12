module Common{
    datatype State = StateValue(pointer: int, memory: seq<int>, output: seq<char>)
    datatype Program = Program(commands: seq<char>, pointer: int, input: seq<char>)
    datatype IntermediateRep = IntermediateRep(commands: seq<Instr>, pointer: int)
    datatype Instr =
        | Inc(n: int)
        | Move(n: int)
        | UserInput(c: char)
        | Print
        | Loop(IntermediateRep)

    function InitialMemory(): seq<int>
    {
    [0, 0, 0, 0, 0]
    }

    function InitialState(): State
    {
        StateValue(0, InitialMemory(), [])
    }

    predicate valid_program(p: Program)
    {
    |p.commands| > 0 
        && 0<= p.pointer <= |p.commands|
        && (forall i:: (0<= i < |p.commands| ==> p.commands[i] in [',', '[', ']', '.', '+', '-', '>', '<']))
        && balanced_brackets(p)
    }

    predicate state_reqs(s: State){
        0 <= s.pointer < |s.memory| && (forall i:: (0<= i < |s.memory|) ==> 0 <= s.memory[i] <= 255)
    }
    predicate valid_loop(p: seq<char>)

    {
        (forall i:: (0<=i < |p| ==> p[i] != '[' && p[i] != ']')) || (exists j, k:: 0<=j < k < |p| && p[j]=='[' && p[k]==']' && valid_loop(p[j+1..k]))
    }

    predicate balanced_counter(p: seq<char>, counter: int)
    decreases p
    {
        if (|p| == 0) then counter == 0
        else if p[0] == '[' then balanced_counter(p[1..], counter+1)
        else if p[0] == ']' then balanced_counter(p[1..], counter+1) && counter > 0
        else true
    }

    predicate balanced_brackets(p: Program)
    {
        balanced_counter(p.commands, 0)
    }
    predicate pointer_moved_up(p: Program, p': Program)
    {
        (p'.pointer == p.pointer + 1) && (p.commands == p'.commands)
    }

    predicate ir_moved_up(ir: IntermediateRep, ir': IntermediateRep)
    {
        ((ir.pointer == |ir.commands|-1 ==ir'.pointer) || (ir'.pointer == ir.pointer + 1)) 

    }
    predicate valid_state(s: State, s': State){
        |s.memory| == |s'.memory|
        && 0 <= s.pointer < |s.memory| && 0 <= s'.pointer < |s.memory|
    }
    predicate aligned_programs(p: Program, p': Program){
        p.commands == p'.commands && 0<=p.pointer <= |p.commands| && 0 <= p'.pointer <= |p.commands|
    }





}
