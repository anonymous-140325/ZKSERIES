package zk.bulletproofs;

import ec.Scalar;

public abstract class ConstraintSystem {

    public abstract void constrain(LinearCombination lc);

    public abstract LRO multiply(LinearCombination l, LinearCombination r);

    public abstract LRO allocateMultiplier(Scalar left, Scalar right);

    public void constrainLCWithScalar(LinearCombination lc, Scalar scalar) {
        constrain(lc.sub(LinearCombination.from(scalar)));
    }
}
