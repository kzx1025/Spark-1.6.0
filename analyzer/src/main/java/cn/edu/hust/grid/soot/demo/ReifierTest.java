package cn.edu.hust.grid.soot.demo;

/**
 * Created by root on 15-8-6.
 */
public class ReifierTest {

    static class Point<T>{
        public double x;
        public T y;

        public void set(double x,T y){
            this.x = x;
            this.y = y;
        }

        public void setX(double x){
            this.x = x;
        }
    }

    public static void main(String[] args){
        Point<Double> over = new Point<Double>();
        over.set(1.0,1.0);
        over.setX(2.0);
        System.out.println("Result:"+over.x+"--"+over.y);
    }
}
