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



    predicate valid_program(p: Program)
    {
    |p.commands| > 0 
        && 0<= p.pointer <= |p.commands|
        && (forall i:: (0<= i < |p.commands| ==> p.commands[i] in [',', '[', ']', '.', '+', '-', '>', '<']))
        && valid_loop(p.commands)

    }

    predicate valid_ir(ir: IntermediateRep)
    {
        0 <= ir.pointer <= |ir.commands| &&
        valid_ir_commands(ir.commands)
    }
    predicate valid_ir_commands(ir: seq<Instr>)
    {
        forall k:: 0<= k < |ir| ==>
            (match ir[k] {
                case Jump(dest, dir) => 0<= dest < |ir|
                case _ => true
            })
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
    predicate empty_body(p: seq<char>)
    {
        (forall i:: (0<=i < |p| ==> p[i] != '[' && p[i] != ']')) 
    }

    predicate valid_loop(p: seq<char>)

    {
        empty_body(p) || 
        (
            forall i:: (0<= i < |p| ==>(
                (p[i]== '[' ==> exists k::  i< k < |p| && p[k]== ']' && valid_loop(p[i+1..k]))
                &&
                (p[i]== ']' ==> exists k::  0<= k < i && p[k]== '[' && valid_loop(p[k+1..i]))
            ))
        )
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
        (ir'.pointer == ir.pointer + 1) && (ir.commands == ir'.commands)

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

    function Changes(p: Program): seq<int>
    ensures increasing_seq(Changes(p))
    {
        if |p.commands|==0 then []
        else if 0< |p.commands| <= 1 then [0]
        else ChangesHelper(p, 0)
    }
    function  ChangesHelper(p: Program, i: int): seq<int>
        requires 0 <= i <= |p.commands|
        ensures increasing_seq(ChangesHelper(p, i))
        decreases |p.commands|-i 
    {
        if i == |p.commands| then []
        else if p.commands[i] in ['+', '-', '<', '>'] then [i] + ChangesHelper(p, i + count_consecutive_symbols(p, i))
        else [i]+ ChangesHelper(p, i + 1)
    }    
    ghost predicate change_helper_correct(p: Program, i: int, res: seq<int>)
    requires 0 <= i <= |p.commands|
    // requires res == ChangesHelper(p, i)
    {
        (i == |p.commands| ==> !(i in res))
        &&
        (i < |p.commands| ==> (
        (i in res && res[0]==i) &&
        (forall d:: 0<= d <|res| ==> 0<= res[d] <|p.commands|)
        &&
        (forall d:: 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '<', '>'] ==> (res[d+1]==res[d]+ count_consecutive_symbols(p, res[d]) && ((p.commands[res[d]]!=p.commands[res[d+1]]))))
        &&
        (forall d:: (0<= d <|res|-1 && !(p.commands[res[d]] in ['+', '-', '<', '>']))==> (res[d+1]-res[d] ==1))
        &&
        (forall d:: (d in res && p.commands[d] in ['+', '-', '<', '>']) ==> ((d+count_consecutive_symbols(p, d) == |p.commands|) || d+count_consecutive_symbols(p, d) in res))
        &&
        (forall d:: (d in res && !(p.commands[d] in ['+', '-', '<', '>'])) ==> ((d+1 == |p.commands| && !(d+1 in res)) || (d+1 < |p.commands| && d+1 in res)))
)
        )
    }
 
    lemma StrictlyIncreasingImpliesUnique(s: seq<int>) 
    requires forall i, j :: 0<= i < j < |s| ==> s[i] < s[j]  // The sequence is strictly increasing
    ensures forall i, j :: i != j && 0<= i < |s| && 0<= j <|s| ==> s[i] != s[j]

{
    // Prove that all elements are unique
}
    ghost predicate int_in_seq(k: int, s: seq<int>){
        k in s
    }

    lemma trivialBiggerNotEq(s: seq<int>, i: int)
    requires forall k:: k in s ==> i > k
    ensures forall k:: int_in_seq(k, s) ==> i!= k 
    {}
    ghost predicate greater_than_and_in_seq( k: int, i: int, s2: seq<int>){
        (i> k && k in s2)
    }

    ghost predicate sub_changes_1_step(p: Program, next_command_indices: seq<int>)
    requires forall d:: 0<= d < |next_command_indices| ==> 0<=next_command_indices[d]<|p.commands|
    {
        forall d :: (0 <= d < |next_command_indices| && !(p.commands[next_command_indices[d]] in ['+', '-', '>', '<'])) ==> next_step(p, next_command_indices[d], 1, next_command_indices)
    }
    ghost predicate next_step(p: Program, i: int, k: int, next_command_indices: seq<int>)
    requires i in next_command_indices
    {
        inside_the_indices(p, next_command_indices, i+k)
    }
    ghost predicate relation_between_old_new(p: Program, old_i: int, i: int, next_command_indices: seq<int>)
    {
        (old_i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i)
    }
    lemma simple_exclusion(symb: char)
    requires symb == '.' || symb == ']'
    ensures !(symb in ['+', '-', '>', '<'])
    {}

    lemma simple_exclusion_2(symb: char)
        requires symb == ',' || symb == '[' 
        ensures !(symb in ['+', '-', '>', '<'])
    {}


    lemma addition_is_preserving(p: Program, old_i: int, i: int, k: int, summation: int, next_command_indices: seq<int>)
    requires summation == i+k
    requires relation_between_old_new(p, old_i, i+k, next_command_indices)
    ensures relation_between_old_new(p, old_i, summation, next_command_indices)
    {
        
    }

    lemma addition_is_preserving_one(p: Program, old_i: int, i: int, summation: int, next_command_indices: seq<int>)
    requires summation == i+1
    requires relation_between_old_new(p, old_i, i+1, next_command_indices)
    ensures relation_between_old_new(p, old_i, summation, next_command_indices)
    {
        
    }

    lemma step_is_indices(p: Program, i: int, k: int, next_command_indices: seq<int>)
    requires (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k)
    requires i in next_command_indices ==> next_step(p, i, k, next_command_indices)
    ensures (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+k)
    {}

    lemma one_step_is_indices(p: Program, i: int, next_command_indices: seq<int>)
        requires (i in next_command_indices && next_step(p, i, 1, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+1)
        requires i in next_command_indices ==> next_step(p, i, 1, next_command_indices)
        ensures (i in next_command_indices) ==> inside_the_indices(p, next_command_indices, i+1)
    {}

    lemma implication_with_and(p: Program, i: int, k: int, next_command_indices: seq<int>)
    ensures (i in next_command_indices && next_step(p, i, k, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+k)
    {}

    lemma implication_with_and_2(p: Program, i: int, next_command_indices: seq<int>)
    requires 0<= i < |p.commands| && !(p.commands[i] in ['+', '-', '>', '<']) 
    ensures (i in next_command_indices && next_step(p, i, 1, next_command_indices)) ==> inside_the_indices(p, next_command_indices, i+1)
    {}

    ghost predicate sub_changes(p: Program, next_command_indices: seq<int>)
    requires forall d:: 0<= d < |next_command_indices| ==> 0<=next_command_indices[d]<|p.commands|
    {
        forall d :: (0 <= d < |next_command_indices| && (p.commands[next_command_indices[d]] in ['+', '-', '>', '<'])) ==> next_step(p, next_command_indices[d], count_consecutive_symbols(p, next_command_indices[d]), next_command_indices)
    }

    predicate inside_the_indices(p: Program, next_command_indices: seq<int>, i: int){
       (i == |p.commands|) || (i < |p.commands| && i in next_command_indices)
    }
    lemma inside_the_indices_sum(p: Program, next_command_indices: seq<int>, i: int, k: int)
    requires i in next_command_indices && inside_the_indices(p, next_command_indices, i+k)
    ensures next_step(p, i, k, next_command_indices)
    {}

    ghost predicate sub_changes_inclusion(p: Program, next_command_indices: seq<int>)
    requires forall d:: 0<= d < |next_command_indices| ==> 0<=next_command_indices[d]<|p.commands|
    {
        forall d:: (d in next_command_indices && p.commands[d] in ['+', '-', '<', '>']) ==> next_step(p, d, count_consecutive_symbols(p, d), next_command_indices) 

    }
    ghost predicate sub_changes_inclusion_1_step(p: Program, next_command_indices: seq<int>)
    requires forall d:: 0<= d < |next_command_indices| ==> 0<=next_command_indices[d]<|p.commands|
    {
        forall d:: (d in next_command_indices && !(p.commands[d] in ['+', '-', '<', '>'])) ==> next_step(p, d, 1, next_command_indices)

    }
    predicate within_length(d: int, s1: seq<int>)
    {
        0<= d < |s1|
    }

    predicate just_short_length(d: int, s1: seq<int>)
    {
        0<=d<|s1|-1
    }

    ghost predicate changes_correct(p: Program, res: seq<int>)
    {
        (forall d:: within_length(d, res) ==>
            (0 <= res[d] < |p.commands| &&
            ( just_short_length(d, res) && p.commands[res[d]] in ['+', '-', '>', '<'] ==>(
                res[d+1] == res[d] + count_consecutive_symbols(p, res[d])
                && res[d+1] != res[d]
            )) &&
            (((p.commands[res[d]] in ['+', '-', '>', '<'])) ==>
                (res[d]+count_consecutive_symbols(p, res[d]) == |p.commands| || (res[d]+count_consecutive_symbols(p, res[d]) < |p.commands| &&res[d]+count_consecutive_symbols(p, res[d]) in res)))    
            &&
            ((within_length(d, res) && !(p.commands[res[d]] in ['+', '-', '>', '<'])) ==>
                ((res[d]+1 == |p.commands| ) || (res[d]+1 < |p.commands| && res[d]+1 in res)))    
            )
            &&
            ( just_short_length(d, res) && !(p.commands[res[d]] in ['+', '-', '>', '<']) ==>(
                res[d+1] == res[d] + 1
            ))
            // &&
            // (d == |res|-1 && !(p.commands[res[d]] in ['+', '-', '>', '<']) ==>
            //     res[d]+1 == |p.commands|
            // )
        )
    }
    predicate increasing_seq (s: seq<int>)
    {
        forall i :: 1 <= i < |s| ==> s[i - 1] < s[i] 
    }
    lemma zero_implies_all (j: int, s1: seq<int>, s2: seq<int>)
    requires j==0
    ensures 1<=j<=|s2| ==> s1[j-1]==s2[j-1]
    {}

    ghost predicate in_bounds_commands(p: Program, res: seq<int>){
        forall d:: within_length(d, res) ==>
            (0 <= res[d] < |p.commands|)
    }
    lemma interpret_changes_correct(p: Program, res: seq<int>)
    requires changes_correct(p, res)
    ensures in_bounds_commands(p, res)
    {}

    lemma in_bounds_commands_implies_not_in(p: Program, res: seq<int>, i: int)
    requires in_bounds_commands(p, res)
    ensures i >= |p.commands| ==> !(i in res)
    {}

    lemma extension (j: int, s1: seq<int>, s2: seq<int>)
    requires 0<= j < |s1|
    requires |s1| == j+1
    requires j < |s2| ==> s1[j]==s2[j]
    requires j <= |s2| ==> s1[..j] == s2[..j]
    ensures j+1 <= |s2| ==> s1 == s2[..j+1]
    {}

    lemma addition_preserving_2 (s1: seq<int>, s2: seq<int>, j: int, k: int)
    requires 0<= j < |s1|
    requires 1<= j+1 <= |s2| ==> s1[j] == s2[j]
    requires k == j+1
    ensures 1<= k <= |s2| ==> s2[k-1] == s2[k-1]
    {}

    lemma greater_not_equal(s1: seq<int>, i: int)
    requires forall k:: k in s1 ==> i>k
    ensures !(i in s1)
    {}


    lemma addition_preserving_3 (s1: seq<int>, s2: seq<int>, j: int, k: int)
    requires 0<= j < |s1|
    requires j+1 <= |s2| ==> s1 == s2[..j+1]
    requires k == j+1
    ensures k <= |s2| ==> s1 == s2[..k]
    {}


    lemma isolate_changes_correct(p: Program, res: seq<int>)
    requires changes_correct(p, res)
    ensures forall d:: 0<=d < |res| ==>
        (0 <= res[d] < |p.commands| &&
            ( 0 <= d < |res|-1 && p.commands[res[d]] in ['+', '-', '>', '<'] ==>(
                res[d+1] == res[d] + count_consecutive_symbols(p, res[d])
                && res[d+1] != res[d]
            ))
        ) 
{}
    function count_consecutive_symbols(p: Program, idx: int): nat
        requires 0 <= idx < |p.commands|
        ensures idx + count_consecutive_symbols(p, idx) <= |p.commands|
        ensures idx+count_consecutive_symbols(p, idx) < |p.commands| && (p.commands[idx] in ['+', '-', '<', '>'])
        ==> (p.commands[idx] != p.commands[idx+count_consecutive_symbols(p, idx)])
        ensures forall j:: idx <= j < idx+count_consecutive_symbols(p, idx) ==> p.commands[j]==p.commands[idx]
        decreases |p.commands|-idx
        {
        if idx + 1 < |p.commands| && p.commands[idx] == p.commands[idx + 1] && p.commands[idx] in ['+', '-', '<', '>'] then
            1 + count_consecutive_symbols(p, idx + 1)
        else 
            1
    }



}
