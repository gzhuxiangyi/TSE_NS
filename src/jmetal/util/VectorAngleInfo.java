package jmetal.util;

public class VectorAngleInfo {
		int targetSolutionId;  // to which the considered solutions have minimum vector angle
		int secdTargetSolutionId;// to which the considered solutions have second minimum vector angle
		double vectorValue;		
		double secdVectorValue;		
		
		public VectorAngleInfo () {
			targetSolutionId = -1;
			secdTargetSolutionId = -1;
			vectorValue = 0.0;
			secdVectorValue = 0.0;
		  }
		
		public int getTargetSolutionId() {
			return targetSolutionId;
		}
		public void setTargetSolutionId(int targetSolutionId) {
			this.targetSolutionId = targetSolutionId;
		}
		public double getVectorValue() {
			return vectorValue;
		}
		public void setVectorValue(double vectorValue) {
			this.vectorValue = vectorValue;
		}
		public int getSecdTargetSolutionId() {
			return secdTargetSolutionId;
		}
		public void setSecdTargetSolutionId(int secdTargetSolutionId) {
			this.secdTargetSolutionId = secdTargetSolutionId;
		}
		public double getSecdVectorValue() {
			return secdVectorValue;
		}
		public void setSecdVectorValue(double secdVectorValue) {
			this.secdVectorValue = secdVectorValue;
		}
		
		
}
