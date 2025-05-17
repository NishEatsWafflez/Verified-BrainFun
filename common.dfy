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
        && (forall i:: (0<= i < |p.commands| ==> p.commands[i] in [',', /*'[', ']',*/ '.', '+', '-', '>', '<']))
        && balanced_brackets(p)
    }

    predicate valid_ir(ir: IntermediateRep)
    {
        0 <= ir.pointer <= |ir.commands|
    }

    predicate state_reqs(s: State){
        0 <= s.pointer < |s.memory| && (forall i:: (0<= i < |s.memory|) ==> 0 <= s.memory[i] <= 255)
    }

    predicate within_ir_range(i: int, ir: IntermediateRep){
        0 <= i < |ir.commands|
    }
    predicate within_program_range(i: int, p: Program, p': Program){
        p.pointer <= i < p'.pointer
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
    ghost predicate matching_pred(s: seq<char>, indices: seq<int>)
    requires forall i:: 0<= i <= |indices|-1 ==> 0 <= indices[i] < |s|
    {
        (|indices| == 0) || (|indices|>0==>
        // true //TODO: write lol
        (forall i:: (0<= i < |indices|-1 ==> forall j:: indices[i] <= j < indices[i+1] ==> (s[j] == s[indices[i]] && s[j] != s[indices[i+1]]))) 
        // &&(forall j:: indices[|indices|-1] <= j < |s| ==> s[j] == s[indices[|indices|-1]])
    )}

    function Changes(p: Program): seq<int>

    // ensures matching_pred(s, Changes(s))
    {
        if |p.commands|==0 then []
        else if 0< |p.commands| <= 1 then [0]
        else ChangesHelper(p, 0)
    }

    ghost predicate change_helper_correct(p: Program, i: int, res: seq<int>)
    requires 0 <= i <= |p.commands|
    // requires res == ChangesHelper(p, i)
    {
        (i == |p.commands| ==> !(i in res)
        )&&(forall d:: 0<= d <|res| ==> 0<= res[d] <|p.commands|
        )&&(forall d:: 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '<', '>'] ==> res[d+1]==res[d]+ count_consecutive_symbols(p, res[d])
        )&&(forall d:: 0<= d <|res|-1 && p.commands[res[d]] in ['+', '-', '<', '>']==> ((p.commands[res[d]]!=p.commands[res[d+1]]))
        )&&(forall d:: (0<= d <|res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>']))==> (res[d+1]-res[d] ==1)
        )&&(forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in res)
        )&&(forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 >= |p.commands|) || d+1 in res)
)
    }
    function  ChangesHelper(p: Program, i: int): seq<int>
        requires 0 <= i <= |p.commands|
        decreases |p.commands|-i 
        // ensures change_helper_correct(p, i, ChangesHelper(p, i))
        // ensures i == |p.commands| ==> !(i in ChangesHelper(p, i))
        // // ensures forall d:: (d in ChangesHelper(p, i) && p.commands[d] in ['+', '-', '<', '>']  && d + count_consecutive_symbols(p, d) < |p.commands|) ==> d+ count_consecutive_symbols(p, d) in ChangesHelper(p, i)
        // ensures forall d:: 0<= d <|ChangesHelper(p, i)| ==> 0<= ChangesHelper(p, i)[d] <|p.commands|
        // ensures forall d:: 0 <= d < |ChangesHelper(p, i)|-1 && p.commands[ChangesHelper(p, i)[d]] in ['+', '-', '<', '>'] ==> ChangesHelper(p, i)[d+1]==ChangesHelper(p, i)[d]+ count_consecutive_symbols(p, ChangesHelper(p, i)[d])
        // // ensures forall d:: 0<= d < |ChangesHelper(p, i)|-1 && p.commands[ChangesHelper(p, i)[d]] in ['+', '-', '<', '>'] ==> ChangesHelper(p, i)[d+1]-ChangesHelper(p, i)[d] == count_consecutive_symbols(p, ChangesHelper(p, i)[d])
        // ensures forall d:: 0<= d <|ChangesHelper(p, i)|-1 && p.commands[ChangesHelper(p, i)[d]] in ['+', '-', '<', '>']==> ((p.commands[ChangesHelper(p, i)[d]]!=p.commands[ChangesHelper(p, i)[d+1]]))
        // ensures forall d:: (0<= d <|ChangesHelper(p, i)|-1 && !(p.commands[ChangesHelper(p, i)[d]] in ['+', '-', '<', '>']))==> (ChangesHelper(p, i)[d+1]-ChangesHelper(p, i)[d] ==1)
        // ensures forall d:: (d in ChangesHelper(p, i) && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) >= |p.commands|) || d+count_consecutive_symbols(p, d) in ChangesHelper(p, i))
        // ensures forall d:: (d in ChangesHelper(p,i) && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 >= |p.commands|) || d+1 in ChangesHelper(p,i))

        // ensures forall d:: 0<=d<|ChangesHelper(s, i)|-1 ==> forall j:: ChangesHelper(s, i)[d] <= j < ChangesHelper(s, i)[d+1] ==> s[j] != s[ChangesHelper(s, i)[d+1]]
        // ensures matching_pred(s, ChangesHelper(s, i))
    {
        if i == |p.commands| then []
        else if p.commands[i] in ['+', '-', '<', '>'] then [i] + ChangesHelper(p, i + count_consecutive_symbols(p, i))
        else [i]+ ChangesHelper(p, i + 1)
    }    
    function count_consecutive_symbols(p: Program, idx: int): nat
        requires 0 <= idx < |p.commands|
        ensures idx + count_consecutive_symbols(p, idx) <= |p.commands|
        ensures idx+count_consecutive_symbols(p, idx) < |p.commands| && (p.commands[idx] in ['+', '-', '<', '>'])==> (p.commands[idx] != p.commands[idx+count_consecutive_symbols(p, idx)])
        ensures forall j:: idx <= j < idx+count_consecutive_symbols(p, idx) ==> p.commands[j]==p.commands[idx]
        decreases |p.commands|-idx
        {
        if idx + 1 < |p.commands| && p.commands[idx] == p.commands[idx + 1] && p.commands[idx] in ['+', '-', '<', '>'] then
            1 + count_consecutive_symbols(p, idx + 1)
        else 
            1
    }
}
