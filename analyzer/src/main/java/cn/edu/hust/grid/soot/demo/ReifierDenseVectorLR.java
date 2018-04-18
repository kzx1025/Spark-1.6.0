package cn.edu.hust.grid.soot.demo;

import java.io.Serializable;
import java.util.Random;

/**
 * Created by root on 15-8-10.
 */

interface Function2<T1, T2, R>  {
    public R call(T1 v1, T2 v2);
}

interface Function3<T1,T2,T3,R> {
    public R call(T1 v1,T2 v2,T3 v3);
}

class ReifierDenseVector<T> {
    private T[] data;

    private Function2 _dot;
    private Function2 _plus;
    private Function3 _multip;

    ReifierDenseVector(T[] data){
        this.data = data;
        if (data.getClass().getComponentType().getSimpleName().equals("Double")) {
            _dot = new Function2<Double[], Double[], Double>() {
                @Override
                public Double call(Double[] a, Double[] b) {
                    double x = 0;
                    for (int i = 0; i < b.length; i++) {
                        x += a[i] * b[i];
                    }
                    return x;
                }
            };
            _plus = new Function2<Double[], Double[], Double[]>() {
                @Override
                public Double[] call(Double[] a, Double[] b) {
                    Double[] x = new Double[b.length];
                    for( int i = 0; i< x.length;  i++) {
                        x[i] = 0.0;
                    }
                    for (int i = 0; i < b.length; i++) {
                         x[i] = a[i] + b[i];
                    }
                    return x;
                }
            };
            _multip = new Function3<Double[], Integer, Double, Double>() {
                @Override
                public Double call(Double[] a, Integer i, Double b) {
                    return a[i]*b;
                }
            };
        } else if(data.getClass().getComponentType().getSimpleName().equals("Integer") ){
            _dot = new Function2<Integer[], Integer[], Integer>() {
                @Override
                public Integer call(Integer[] a, Integer[] b) {
                    int x = 0;
                    for (int i = 0; i < b.length; i++) {
                        x += a[i] * b[i];
                    }
                    return x;
                }
            };
            _plus = new Function2<Integer[], Integer[], Integer[]>() {
                @Override
                public Integer[] call(Integer[] a, Integer[] b) {
                    Integer[] x = new Integer[b.length];
                    for (int i = 0; i < b.length; i++) {
                        x[i] = a[i] + b[i];
                    }
                    return x;
                }
            };
            _multip = new Function3<Integer[], Integer, Integer, Integer>() {
                @Override
                public Integer call(Integer[] a, Integer i, Integer b) {
                    return a[i]*b;
                }
            };
        } else {
            _dot = new Function2<Object[], Object[], Object>() {
                @Override
                public Object call(Object[] v1, Object[] v2) {
                    throw new UnsupportedOperationException();
                }
            };
            _plus = new Function2<Object[], Object[], Object[]>() {
                @Override
                public Object[] call(Object[] v1, Object[] v2) {
                    throw new UnsupportedOperationException();
                }
            };
            _multip = new Function3<Object[], Object, Object,Object>() {
                @Override
                public Object call(Object[] v1, Object v2, Object v3) {
                    throw new UnsupportedOperationException();
                }
            };
        }
    }

    public int length(){
        return this.data.length;
    }

    public void fill(T element, int offset){
        this.data[offset] = element;
    }

    public T dot(ReifierDenseVector<T> other) {
        return (T) _dot.call(data, other.data);
    }

    public void plus(ReifierDenseVector<T> other) {
        this.data = (T[]) _plus.call(data, other.data);
    }

    public T multip(int offset, T other){
        return (T) _multip.call(data, offset, other);
    }

}

public class ReifierDenseVectorLR {
    private static final int D = 10;   // Number of dimensions
    private static final int N = 200;  // Number of data points
    private static final Random rand = new Random(42);
    private static final double R = 0.7;  // Scaling factor

    private static final ReifierDenseVector<Double> w = new ReifierDenseVector(new Double[D]);

    static {
        for (int i = 0; i < D; i++) {
            w.fill(2 * rand.nextDouble() - 1, i);
        }
    }

    static class DataPoint implements Serializable {
        DataPoint(ReifierDenseVector<Double> x, double y) {
            this.x = x;
            this.y = y;
        }

        ReifierDenseVector<Double> x;
        double y;
    }

    private static DataPoint[] points = new DataPoint[N];

    public static void f() {
        for (int i = 0; i < N; i++) {
            int y;
            if (i % 2 == 0)
                y = 0;
            else
                y = 1;
            ReifierDenseVector<Double> x = new ReifierDenseVector<Double>(new Double[D]);
            for (int j = 0; j < D; j++) {
               x.fill(rand.nextGaussian() + y * R,j);
            }

            points[i] = new DataPoint(x, y);
        }
    }

    public static void g() {
        Double[] fornew = new Double[D];
        for(int i =0;i<D;i++)
            fornew[i]=0.0;
        ReifierDenseVector<Double> gradient = new ReifierDenseVector<Double>(fornew);
        for (int i = 0; i < N; i++) {
            DataPoint p = points[i];
            ReifierDenseVector<Double> subGradient = new ReifierDenseVector<Double>(fornew);
            for (int j = 0; j < D; j++) {
                double dot = w.dot(p.x);
                subGradient.fill(p.x.multip(j,(1 / (1 + Math.exp(-p.y * dot)) - 1)*p.y),j);
            }
            gradient.plus(subGradient);
        }
        System.out.println(gradient);
    }

    public static void main(String[] args) {

        f();
        g();
    }
}
