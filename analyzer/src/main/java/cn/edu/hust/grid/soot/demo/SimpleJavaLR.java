package cn.edu.hust.grid.soot.demo;

import java.io.Serializable;
import java.util.Arrays;

/**
 * Created by peicheng on 15-7-28.
 */
public final class SimpleJavaLR {
    private static final int D = 10;   // Number of dimensions
    private static final int N = 1000;  // Number of data points
    private static final double R = 0.00007;  // Scaling factor

    private static final double[] w;

    static {
        w = new double[D];
        for (int i = 0; i < D; i++) {
            w[i] = 2 * i * 0.037 - 1;
        }
    }

    static class DataPoint implements Serializable {
        DataPoint(double[] x, double y) {
            this.x = x;
            this.y = y;
        }

        double[] x;
        double y;
    }

    public static double dot(double[] a, double[] b) {
        double x = 0;
        for (int i = 0; i < D; i++) {
            x += a[i] * b[i];
        }
        return x;
    }

    private static DataPoint[] cache;

    public static double[] apply(boolean withCache) {
        if (!withCache) {
            cache = new DataPoint[N];
            f();
        }
        return g();
    }

    public static void f() {
        DataPoint[] points = cache;
        for (int i = 0; i < N; i++) {
            int y;
            if (i % 2 == 0)
                y = 0;
            else
                y = 1;
            double[] x = new double[D];
            for (int j = 0; j < D; j++) {
                x[j] =  i * 0.000013 + j * 0.00079 + y * R;
            }

            points[i] = new DataPoint(x, y);
        }
    }

    public static double[] g() {
        DataPoint[] points = cache;
        double[] gradient = new double[D];
        for (int i = 0; i < N; i++) {
            DataPoint p = points[i];
            double[] subGradient = new double[D];
            for (int j = 0; j < D; j++) {
                double dot = dot(w, p.x);
                subGradient[j] = (1 / (1 + Math.exp(-p.y * dot)) - 1) * p.y * p.x[j];
            }
            for (int j = 0; j < D; j++) {
                gradient[j] += subGradient[j];
            }

        }

        return gradient;
    }

    public static void printWeights(double[] a) {
        System.out.println(Arrays.toString(a));
    }

    public static void main(String[] args) {
        System.out.print("Initial w: ");
        printWeights(w);

        double[] gradient = apply(false);
        printWeights(gradient);
        for (int j = 0; j < D; j++) {
            w[j] -= gradient[j];
        }
        for (int i = 1; i < 3; i++) {
            gradient = apply(true);
            printWeights(gradient);
            for (int j = 0; j < D; j++) {
                w[j] -= gradient[j];
            }
        }

        System.out.print("Final w: ");
        printWeights(w);
    }
}
