pipeline {
    
    agent any
    
    tools {
        maven 'Maven 3.5.2'
    }

    stages {
        stage ('Initialize') {
            steps {
                sh '''
                    echo "PATH = ${PATH}"
                    echo "M2_HOME = ${M2_HOME}"
                '''
            }
        }


        stage ('Test') {
            steps {
                sh 'mvn test' 
            }
        }
    }
}