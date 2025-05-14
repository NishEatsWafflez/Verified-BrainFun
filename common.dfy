module Common{
    datatype State = StateValue(pointer: int, memory: seq<int>, output: seq<char>)
    datatype Program = Program(commands: seq<char>, pointer: int, input: seq<char>)
    datatype IntermediateRep = IntermediateRep(commands: seq<Instr>, pointer: int, input: seq<char>)
    datatype Instr =
        | Inc(n: int)
        | Move(n: int)
        | UserInput
        | Print
        | Jump(dest: int, direction: bool) //True is forwards, false is backwards (basically if this should be a backwards jump)

    function InitialMemory(): seq<int>
    {
    [0, 0, 0, 0, 0] // TODO: fix to be larger
    }

    function InitialState(): State
    // ensures StateValue(0, InitialMemory(), [])
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

    predicate valid_ir(ir: IntermediateRep)
    {
        0 <= ir.pointer <= |ir.commands|
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
        if |p| == 0 then counter == 0
        else if p[0] == '[' then balanced_counter(p[1..], counter + 1)
        else if p[0] == ']' then counter > 0 && balanced_counter(p[1..], counter - 1)
        else balanced_counter(p[1..], counter)
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

    predicate in_sync_irs(ir: IntermediateRep, ir': IntermediateRep){
        ir.commands == ir'.commands
    }

    predicate valid_input(input: seq<char>){
        forall i:: 0 <= i < |input| ==> 0 <= input[i] as int<= 255
    }


    // predicate enough_input(p: Program)
    // requires valid_program(p){
    //     |p.input| == |(set i | p.pointer <=i < |p.commands| && p.commands[i] == ',')|
    // }

}
