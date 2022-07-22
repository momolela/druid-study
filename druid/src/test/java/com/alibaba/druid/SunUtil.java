package com.alibaba.druid;

import com.alibaba.druid.pool.DruidDataSource;
import com.alibaba.druid.pool.DruidPooledConnection;

import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLException;

public class SunUtil {

    public static void main(String[] args) {
        DruidDataSource druidDataSource = new DruidDataSource();

        druidDataSource.setUrl("jdbc:oracle:thin:@10.10.2.45:1521:hip40");
        druidDataSource.setUsername("BSHIP_BASE");
        // druidDataSource.setUserCallback();
        druidDataSource.setPassword("BSOFT");
        druidDataSource.setDriverClassName("oracle.jdbc.driver.OracleDriver");
        druidDataSource.setDbType("oracle");

        // 设置 druid 配置参数
        druidDataSource.setInitialSize(5);
        druidDataSource.setMinIdle(5);
        druidDataSource.setMaxActive(20);
        druidDataSource.setMaxWait(10000);

        // 设置过滤器链
        try {
            druidDataSource.setFilters("stat,wall,mergeStat");
        } catch (SQLException e) {
            e.printStackTrace();
        }

        // 获取连接执行
        DruidPooledConnection connection = null;
        PreparedStatement preparedStatement = null;
        ResultSet rs = null;
        try {
            connection = druidDataSource.getConnection();
            preparedStatement = connection.prepareStatement("select * from hai_service");
            rs = preparedStatement.executeQuery();
            while (rs.next()) {
                System.out.println(rs.getString(1));
            }
        } catch (SQLException e) {
            e.printStackTrace();
        } finally {
            try {
                if (rs != null) {
                    rs.close();
                }
            } catch (SQLException e) {
                e.printStackTrace();
            }
            try {
                if (preparedStatement != null) {
                    preparedStatement.close();
                }
            } catch (SQLException e) {
                e.printStackTrace();
            }
            try {
                if (connection != null) {
                    connection.close();
                }
            } catch (SQLException e) {
                e.printStackTrace();
            }
        }
    }
}
