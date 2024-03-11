use vstd::{prelude::*, ptr::*, option::*};

verus! {

spec fn P(n:usize) -> bool {
    32*n*n*n - n*n + n == 0
}

fn check_not_cond(n:usize)
{
    while n != 0
        invariant n == n
    {
        break;
    }
    assert(n == 0);
}


fn use_while(n:usize)
{
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n
        ensures P(n)
    {
        i += 1;
        if i == n {
            // i = 100;
            assume(P(n));
            break
        }
        assume(P(n));
    }
    assert(i <= n);
}

fn use_loop(n:usize)
{
    let mut i = 0;
    loop
        invariant_ensures 0 <= i <= n
    {
        if (i < n) {
            i += 1;
        }
        else if i == n {
            i = n;
            break;
        }
    }
    assert(i <= n);
}

fn succeeds(n:usize) -> (ret:usize)
        ensures 0 <= ret <= n
{
    let (mut i, mut j) = (0, 0);
    loop
      invariant_ensures 0 <= i <= n,
                0 == j,
    {
        if i >= n {
            break;
        }
        i += 1;
        if i % 2 == 0 {
            j = 0;
            break; // NOTE: verus checks successfully if there's no break
        }
    }
    assert(0 <= j <= n);
    return j;
}
#[verus::internal(verus_macro)]
fn fails(n: usize) -> usize {
    ::builtin::ensures(|ret: usize|
            [::builtin::spec_chained_cmp(::builtin::spec_chained_le(::builtin::spec_chained_le(::builtin::spec_chained_value(::builtin::spec_literal_nat("0")),
                                ret), n))]);
    let mut j = 0;
    {
        #[allow(non_snake_case)]
        let VERUS_loop_result =
            match ::core::iter::IntoIterator::into_iter(0..n)
                {
                    #[allow(non_snake_case)]
                    mut VERUS_exec_iter => {
                    #[allow(non_snake_case)]
                    #[verus::internal(spec)]
                    let mut VERUS_ghost_iter;

                    #[verifier::proof_block]
                    {
                        VERUS_ghost_iter =
                            ::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(&VERUS_exec_iter);
                    }

                    #[verus::internal(for_loop)]
                    loop {
                        ::builtin::invariant_ensures([#[verifier::custom_err("For-loop iterator invariant failed. This may indicate a bug in the definition of the ForLoopGhostIterator. You might try using a `loop` instead of a `for`.")] ::vstd::pervasive::ForLoopGhostIterator::exec_invariant(&VERUS_ghost_iter,
                                        &VERUS_exec_iter),
                                    #[verifier::custom_err("Automatically generated loop invariant failed. You can disable the automatic generation by adding #[verifier::no_auto_loop_invariant] to the loop. You might also try storing the loop expression in a variable outside the loop (e.g. `let e = 0..10; for x in e { ... }`).")] ::vstd::pervasive::ForLoopGhostIterator::ghost_invariant(&VERUS_ghost_iter,
                                        builtin::infer_spec_for_loop_iter(&::vstd::pervasive::ForLoopGhostIteratorNew::ghost_iter(&::core::iter::IntoIterator::into_iter(0..n)),
                                            true)),
                                    {
                                        let i =
                                            ::vstd::pervasive::ForLoopGhostIterator::ghost_peek_next(&VERUS_ghost_iter).unwrap_or(::vstd::pervasive::arbitrary());
                                        ::builtin::spec_chained_cmp(::builtin::spec_chained_le(::builtin::spec_chained_le(::builtin::spec_chained_value(::builtin::spec_literal_nat("0")),
                                                    j), n))
                                    }]);
                        ::builtin::ensures([::vstd::pervasive::ForLoopGhostIterator::ghost_ensures(&VERUS_ghost_iter)]);
                        {
                            #[allow(non_snake_case)]
                            let mut VERUS_loop_next;
                            match ::core::iter::Iterator::next(&mut VERUS_exec_iter) {
                                ::core::option::Option::Some(VERUS_loop_val) => {
                                    VERUS_loop_next = VERUS_loop_val;
                                }
                                ::core::option::Option::None => break,
                            };
                            let i = VERUS_loop_next;
                            let () = { if i % 2 == 0 { j = i;
                                                       assert(::vstd::pervasive::ForLoopGhostIterator::exec_invariant(&VERUS_ghost_iter, &VERUS_exec_iter));
                                                       break; } };
                        }

                        #[verifier::proof_block]
                        {
                            VERUS_ghost_iter =
                                ::vstd::pervasive::ForLoopGhostIterator::ghost_advance(&VERUS_ghost_iter,
                                    &VERUS_exec_iter);
                        }
                    }
                }
            };
        VERUS_loop_result
    }
    return j;
}

/*
fn fails(n:usize) -> (ret:usize)
        ensures 0 <= ret <= n
{
    let mut j = 0;
    for i in 0..n
      invariant 0 <= j <= n
    {
        if i % 2 == 0 {
            j = i;
            break; // NOTE: verus checks successfully if there's no break
        }
    }
    return j;
}*/

fn main() {}
}
