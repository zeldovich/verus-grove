#!/usr/bin/env python3

import os
def main():
    orig = ""
    dir_path = os.path.dirname(os.path.realpath(__file__))
    with open(os.path.join(dir_path, "paxos.rs"), "r") as f:
        orig = f.read()

    output = (orig
              .replace("⟦", "")
              .replace("⟨", "")
              .replace("⟧", "_res")
              .replace("⟩", "_prop")
              .replace("γ", "gamma")
              .replace("σ", "sigma")
              .replace("□", "intuitionistically")
              .replace("∀", "forall")
              .replace("∃", "exists")
              .replace("⌜", "|_p| {")
              .replace("⌝", "}")
              .replace("£", "lc")
              .replace("[∗ set]", "big_sepS")
              .replace("-∗", "wand")
              .replace("∗", "sep")
              .replace("∨", "or")
              .replace("⊤", "top_mask")
              .replace("∅", "empty_mask")
              )
    print(output)

if __name__=="__main__":
    main()
