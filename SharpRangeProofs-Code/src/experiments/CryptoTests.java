package experiments;

import java.math.BigInteger;
import java.security.NoSuchAlgorithmException;

import ec.ECPoint;
import zk.bulletproofs.PedersenCommitment;

public class CryptoTests {
	
	public void testCommitSum(PedersenCommitment pc) {		
		BigInteger x1 = BigInteger.valueOf(10);
		BigInteger x2 = BigInteger.valueOf(20);
		BigInteger x3 = BigInteger.valueOf(30);
		
		BigInteger r1 = BigInteger.valueOf(1000);
		BigInteger r2 = BigInteger.valueOf(2000);
		BigInteger r3 = BigInteger.valueOf(3000);
		
		ECPoint C1 = pc.commit(x1, r1).decompress();
		ECPoint C2 = pc.commit(x2, r2).decompress();
		ECPoint C3 = pc.commit(x3, r3).decompress();
		
		ECPoint C3b = C1.add(C2);
		System.out.println(C3.equals(C3b));
		System.out.println(C3.equals(C2) == false);
		System.out.println(C1.equals(C3b) == false);
	}
	
	public void testCommitZero(PedersenCommitment pc) {		
		BigInteger x1 = BigInteger.valueOf(0);
		BigInteger x2 = BigInteger.valueOf(20);
		
		BigInteger r1 = BigInteger.valueOf(0);
		BigInteger r2 = BigInteger.valueOf(4000);
		
		ECPoint C1 = pc.commit(x1, r1).decompress();
		ECPoint C2 = pc.commit(x2, r2).decompress();
		
		ECPoint C2b = C2.add(C1);
		System.out.println(C2.equals(C2b));
		System.out.println(C1.equals(C2b) == false);
	}
	
	public void testCommitNegative(PedersenCommitment pc) {		
		// v negative, r positive
		
		BigInteger x10n = BigInteger.valueOf(-10);
		BigInteger x10 = BigInteger.valueOf(10);
		BigInteger x20 = BigInteger.valueOf(20);
		BigInteger x30 = BigInteger.valueOf(30);
		
		BigInteger r1000n = BigInteger.valueOf(-1000);
		BigInteger r1000 = BigInteger.valueOf(1000);
		BigInteger r2000 = BigInteger.valueOf(2000);
		BigInteger r3000 = BigInteger.valueOf(3000);
		
		ECPoint C1 = pc.commit(x10n, r1000).decompress();
		ECPoint C2 = pc.commit(x10, r2000).decompress();
		ECPoint C3 = pc.commit(x20, r1000).decompress();
		
		ECPoint C1b = C2.subtract(C3);
		System.out.println(C1.equals(C1b));
		System.out.println(C2.equals(C1) == false);
		System.out.println(C3.equals(C1b) == false);
		
		ECPoint C4 = pc.commit(x20, r3000).decompress();
		ECPoint C5 = pc.commit(x30, r2000).decompress();
		ECPoint C5b = C4.subtract(C1b);
		
		System.out.println(C5.equals(C5b));
		
		// v positive r negative 
		
		C1 = pc.commit(x10, r1000n).decompress();
		C2 = pc.commit(x20, r1000).decompress();
		C3 = pc.commit(x10, r2000).decompress();
		
		C1b = C2.subtract(C3);
		System.out.println(C1.equals(C1b));
		System.out.println(C2.equals(C1) == false);
		System.out.println(C3.equals(C1b) == false);
		
		// v negative r negative 
		
		C1 = pc.commit(x10n, r1000n).decompress();
		C2 = pc.commit(x10, r1000).decompress();
		C3 = pc.commit(x20, r2000).decompress();
		
		C1b = C2.subtract(C3);
		System.out.println(C1.equals(C1b));
		System.out.println(C2.equals(C1) == false);
		System.out.println(C3.equals(C1b) == false);
	}
	
	public void testCommitOverflow(PedersenCommitment pc) {
		int N = 100;
		BigInteger V = BigInteger.ONE;
		BigInteger R = BigInteger.ONE;
		
		BigInteger order = new BigInteger("7237005577332262213973186563042994240857116359379907606001950938285454250989");
		
		for(int i=0;i<N;i++) {
			V = V.multiply(BigInteger.TEN);
			R = R.multiply(BigInteger.TEN);
			
			ECPoint C1 = pc.commit(V, R).decompress();
			ECPoint C2 = pc.commit(V.multiply(BigInteger.TWO), R.multiply(BigInteger.TWO)).decompress();
			
			ECPoint C2b = C1.add(C1);
			System.out.println(V.compareTo(order)+" "+C2.equals(C2b));
		}
		
		V = order.subtract(BigInteger.valueOf(N/2));
		R = order.subtract(BigInteger.valueOf(N/4));
		
		for(int i=0;i<N;i++) {
			V = V.add(BigInteger.ONE);
			R = R.add(BigInteger.ONE);
			
			ECPoint C1 = pc.commit(V, R).decompress();
			ECPoint C2 = pc.commit(V.multiply(BigInteger.TWO), R.multiply(BigInteger.TWO)).decompress();
			
			ECPoint C2b = C1.add(C1);
			System.out.println(V.compareTo(order)+" "+C2.equals(C2b));
		}
	}
	
	public void printOrder() {
		BigInteger order = BigInteger.TWO.pow(252).add(new BigInteger("27742317777372353535851937790883648493"));
		System.out.println(order);
	}
	
	public static void main(String[] a) {
		PedersenCommitment pc = null;
		try {
			pc = PedersenCommitment.getDefault();
		} catch (NoSuchAlgorithmException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		new CryptoTests().testCommitSum(pc);
		new CryptoTests().testCommitZero(pc);
		new CryptoTests().testCommitNegative(pc);
		new CryptoTests().testCommitOverflow(pc);
//		new CryptoTests().printOrder();
	}
}
