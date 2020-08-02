import React from 'react'
import styles from './header.module.css'
import { MenuItem } from '../../models'

interface HeaderProps {
    leftContent?: any
    rightContent?: any
    pageName?: any
    menu?: MenuItem[]
}

export default function Header(props: HeaderProps) {
    return (
        <div className={styles.headerContainer}>
            {props.pageName && (
                <div className={styles.pageNameContent}>{props.pageName}</div>
            )}
            <div className={styles.headerLeftContent}>{props.leftContent}</div>
            <div className={styles.headerRightContent}>
                {props.rightContent}
            </div>
        </div>
    )
}
