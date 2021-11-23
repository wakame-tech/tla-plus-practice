------------------------------ MODULE knapsack ------------------------------


EXTENDS TLC, Integers, Sequences

CONSTANTS Capacity, Items

ValueRange == 0..3
SizeRange == 1..4

PT == INSTANCE PT
P == INSTANCE Point WITH X <- 1, Y <- 2

ASSUME Capacity > 0

ItemParams == [size: SizeRange, value: ValueRange]

ItemSamples == {
    [item |-> "a", size |-> 1, value |-> 1], 
    [item |-> "b", size |-> 2, value |-> 3], 
    [item |-> "c", size |-> 3, value |-> 1]
}

ItemSets == [Items -> ItemParams]

KnapsackSize(sack, itemset) ==
    LET
        size_for(item) == itemset[item].size * sack[item]
    IN
        PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

KnapsackValue(sack, itemset) ==
    LET
        value_for(item) == itemset[item].value * sack[item]
    IN
        PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

\* �ｿｽS�ｿｽﾄゑｿｽ { �ｿｽA�ｿｽC�ｿｽe�ｿｽ�ｿｽ�ｿｽ�ｿｽ: �ｿｽﾂ撰ｿｽ } �ｿｽﾌナ�ｿｽb�ｿｽv�ｿｽU�ｿｽb�ｿｽN�ｿｽﾉ対ゑｿｽ�ｿｽﾄ容�ｿｽﾊ以会ｿｽ�ｿｽ�ｿｽ�ｿｽ�ｿｽ�ｿｽ閧ｷ�ｿｽ�ｿｽ
ValidKnapsacks(itemset) ==
    { sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity }
        
BestKnapsack(itemset) ==
    LET
        all == ValidKnapsacks(itemset)
        \* max
        best == CHOOSE best \in all:
            \A worse \in all \ {best}:
                KnapsackValue(best, itemset) >= KnapsackValue(worse, itemset)
        value_of_best == KnapsackValue(best, itemset)
    IN 
        { k \in all: value_of_best = KnapsackValue(k, itemset) }

=============================================================================
