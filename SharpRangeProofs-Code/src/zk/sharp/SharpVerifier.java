package zk.sharp;

import java.math.BigInteger;
import java.security.NoSuchAlgorithmException;
import java.util.Random;

import ec.CompressedRistrettoPoint;
import ec.ECPoint;
import zk.bulletproofs.PedersenCommitment;
import zk.bulletproofs.BpProver;
import zk.bulletproofs.Transcript;
import zk.bulletproofs.Utils;

public class SharpVerifier {
	
	Random generator;
	
	PedersenCommitment pc;
	Transcript transcript;
	BpProver prover;
	
	public SharpVerifier() throws NoSuchAlgorithmException {
		pc = PedersenCommitment.getDefault();
		generator = new Random();
		transcript = new Transcript();
		prover = new BpProver(transcript, pc);
	}
	
	public boolean verify(SharpProof p, BigInteger B, BigInteger L) {
		int N = p.z_x.length;
		int R = p.tau.length;
		
		// line 2-3 (verifier): verify the shortness of the zetas
		
		for(int i=0;i<p.zeta.length;i++) {
			if(p.zeta[i].compareTo(B.multiply(BigInteger.valueOf(4)).multiply(BigInteger.valueOf(N)).multiply(L)) > 0) return false;
		}
		
		byte[] challenge1 = SharpUtils.fiatShamir(p.C_x, p.C_y, B, N, R);
		boolean[] gammas1 = SharpUtils.drawBooleansFromSeed(challenge1, N * 4 * R);
		
		boolean[][][] gamma = new boolean[N][4][R];
		
		for(int i=0;i<N;i++) {
			for(int j=0;j<4;j++) {
				for(int k=0;k<R;k++) {
					gamma[i][j][k] = gammas1[4 * R * i + R * j + k];
				}
			}
		}
		
		byte[] challenge2 = SharpUtils.fiatShamir(p.C_x, p.C_y, B, N, R);
		BigInteger gamma_star = SharpUtils.drawNumberFromSeed(challenge2);
		
//		System.out.println(gamma_star);
		
		// line 5 (verifier): compute F_x
		
		BigInteger sum_z_x = BigInteger.ZERO;
		for(int i=0;i<N;i++) {
			sum_z_x = sum_z_x.add(p.z_x[i]);
		}
		
//		System.out.println(sum_z_x);
		
		ECPoint F_x_term1 = prover.commit(Utils.scalar(sum_z_x), Utils.scalar(p.t_x)).getCommitment().decompress();
		ECPoint F_x_term2 = new CompressedRistrettoPoint(p.C_x.getCommitment().toByteArray()).decompress().multiply(Utils.scalar(gamma_star));
		ECPoint F_x = F_x_term1.subtract(F_x_term2);
		
//		System.out.println(F_x.equals(p.D_x.getCommitment().decompress()));
		if (!F_x.equals(p.D_x.getCommitment().decompress())) return false;
		
		// line 6 (verifier): compute F_y
		
		BigInteger sum_z_y_tau = BigInteger.ZERO;
		for(int i=0;i<N;i++) {
			for(int j=0;j<3;j++) {
				sum_z_y_tau = sum_z_y_tau.add(p.z_y[i][j]);
			}
		}
		
		for(int k=0;k<R;k++) {
			sum_z_y_tau = sum_z_y_tau.add(p.tau[k]);
		}
		
		ECPoint F_y_term1 = prover.commit(Utils.scalar(sum_z_y_tau), Utils.scalar(p.t_y)).getCommitment().decompress();
		ECPoint F_y_term2 = new CompressedRistrettoPoint(p.C_y.getCommitment().toByteArray()).decompress().multiply(Utils.scalar(gamma_star));
		ECPoint F_y = F_y_term1.subtract(F_y_term2);
		
//		System.out.println(F_y.equals(p.D_y.getCommitment().decompress()));
		if(!F_y.equals(p.D_y.getCommitment().decompress())) return false;
		
		// line 7, 8: compute f
		
		BigInteger[] f = new BigInteger[R];
		for(int k=0;k<R;k++) {
			f[k] = p.tau[k];
			for(int i=0;i<N;i++) {
				for(int j=0;j<3;j++) {
					if(gamma[i][j][k]) {
						f[k] = f[k].add(p.z_y[i][j]);
					}
				}
				if(gamma[i][3][k]) {
					f[k] = f[k].add(p.z_x[i]);
				}
			}
			f[k] = f[k].subtract(gamma_star.multiply(p.zeta[k]));
			
//			System.out.println("k="+k+": "+f[k].equals(p.d[k]));
			if(!f[k].equals(p.d[k])) return false;
		}
		
		// line 9: compute f^star
		
		BigInteger[] f_star_pos = new BigInteger[N];
		BigInteger[] f_star_neg = new BigInteger[N];
		for(int i=0;i<N;i++) {
			BigInteger term1 = BigInteger.valueOf(4).multiply(p.z_x[i]).multiply(gamma_star).multiply(B);
			BigInteger term2 = BigInteger.valueOf(4).multiply(p.z_x[i]).multiply(p.z_x[i]);
			BigInteger term3 = gamma_star.multiply(gamma_star);
			BigInteger term4a = p.z_y[i][0].multiply(p.z_y[i][0]);
			BigInteger term4b = p.z_y[i][1].multiply(p.z_y[i][1]);
			BigInteger term4c = p.z_y[i][2].multiply(p.z_y[i][2]);
			
			f_star_neg[i] = term1.add(term3);
			f_star_pos[i] = term2.add(term4a).add(term4b).add(term4c);
		}
		
		// line 10: compute F_star
		BigInteger sum_fstar_pos = BigInteger.ZERO;
		BigInteger sum_fstar_neg = BigInteger.ZERO;
		for(int i=0;i<N;i++) {
			sum_fstar_pos = sum_fstar_pos.add(f_star_pos[i]);
			sum_fstar_neg = sum_fstar_neg.add(f_star_neg[i]);
		}
		
		ECPoint ec_sum_fstar_pos = pc.commit(Utils.scalar(sum_fstar_pos), Utils.scalar(p.t_star.multiply(BigInteger.TWO))).decompress();
		ECPoint ec_sum_fstar_neg = pc.commit(Utils.scalar(sum_fstar_neg), Utils.scalar(p.t_star)).decompress();
		ECPoint F_star_term1 = ec_sum_fstar_pos.subtract(ec_sum_fstar_neg);

		ECPoint F_star_term2 = new CompressedRistrettoPoint(p.C_star.getCommitment().toByteArray()).decompress().multiply(Utils.scalar(gamma_star));
		ECPoint F_star = F_star_term1.subtract(F_star_term2);
		
//		System.out.println(F_star.equals(p.D_star.getCommitment().decompress()));
		if(!F_star.equals(p.D_star.getCommitment().decompress())) return false;
		
		return true;
	}

}
