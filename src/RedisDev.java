import io.lettuce.core.RedisClient;
import io.lettuce.core.RedisFuture;
import io.lettuce.core.RedisURI;
import io.lettuce.core.api.StatefulRedisConnection;

import java.util.stream.IntStream;

public class RedisDev {

    public static void main(String[] args) {
//        tryRedis();
        stream();
    }

    private static void stream() {

        IntStream.range(0, 100).parallel()
                .mapToObj(i -> {
                    System.out.println("f1\t" + i);
                    return i;
                }).map(i -> {
                    System.out.println("f2\t" + i);
                    return i;
                }).toList();
    }

    private static void tryRedis() {
//        RedisURI q = RedisURI.Builder.redis("127.0.0.1", 6379).withPassword("mypass").withDatabase(1).build();

        RedisClient redisClient = RedisClient.create("redis://mypass@127.0.0.1:6379/");
        StatefulRedisConnection<String, String> connection = redisClient.connect();

        System.out.println("Connected to Redis");
        String b = connection.sync().get("d");
        System.out.println(b);
        connection.sync().set("a", "c");
        connection.close();
        redisClient.shutdown();
    }
}
